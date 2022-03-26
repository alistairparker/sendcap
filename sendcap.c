/*
 * Copyright (c) 1999 - 2002
 *  Politecnico di Torino.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that: (1) source code distributions
 * retain the above copyright notice and this paragraph in its entirety, (2)
 * distributions including binary code include the above copyright notice and
 * this paragraph in its entirety in the documentation or other materials
 * provided with the distribution, and (3) all advertising materials mentioning
 * features or use of this software display the following acknowledgement:
 * ``This product includes software developed by the Politecnico
 * di Torino, and its contributors.'' Neither the name of
 * the University nor the names of its contributors may be used to endorse
 * or promote products derived from this software without specific prior
 * written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * Major enhancements by Al Parker, IneoQuest Technologies Inc
 */

#include <memory.h>
#include <stdlib.h>
#include <stdio.h>
#ifndef WIN32
#include <sys/socket.h>

#define  TRUE  1
#define  FALSE  0
#endif

#include <pcap.h>

#ifdef WIN32
#include <pcap-int.h>
static pcap_send_queue *squeue;
#else
#include <unistd.h>
#endif

#ifndef uint32_t
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
#endif

static pcap_t *outdesc;

static char* interf = NULL;

static int count = 0;
static int countRepeats = 0;
static int aggressive = 0;
static int interfNumber = 1;
static int morphClientOnly = 0;
static int morphDestinationOnly = 0;
static int optimize = 0;
static int pauseSeconds = 0;
static int quiet = 0;
static int repeat = 0;
static int sendFromMemory = 0;
static int synchronize = 1;
static int translateTo6 = 0;
static int urlMorph = 0;
static int vlanSpecified = 0;
static unsigned truncateLen = 0;
static unsigned short mtu = 1514; // Min packet corresponding to 1500 byte payload + MAC header.
static unsigned short vlan = 0;
static double ploss = 0;
static double pswap = 0;
static double bursting = 1;

static unsigned long long counter = 0;

static int sequenceIP = 0;
static uint32_t sequenceCount = 0;
static uint32_t sequenceStart = 0;

static int sequenceURICount = 0;
static int sequenceURIOffset = 0;
static int sequenceURIStart = 0;

typedef struct mac_header_s
{
  unsigned char dst[ 6 ];  
  unsigned char src[ 6 ];
  unsigned short type; // 0x800
} mac_header;

typedef struct mac_header_vlan_s
{
  unsigned char dst[ 6 ];  
  unsigned char src[ 6 ];
  unsigned short tpid; // 0x8100
  unsigned short bits;
  unsigned short type; // 0x800
} mac_header_vlan;

/* 4 bytes IP address */
typedef struct ip_address_s 
{
  uint8_t byte[ 4 ];
} ip_address;

/* IPv4 header */
typedef struct ip_header
{
  uint8_t    ver_ihl;  // Version (4 bits) + Internet header length (4 bits)
  uint8_t    tos;    // Type of service 
  uint16_t  tlen;    // Total length 
  uint16_t  identification; // Identification
  uint16_t  flags_fo;  // Flags (3 bits) + Fragment offset (13 bits)
  uint8_t    ttl;    // Time to live
  uint8_t    proto;    // Protocol
  uint16_t  crc;    // Header checksum
  ip_address  saddr;    // Source address
  ip_address  daddr;    // Destination address
  //u_int    op_pad;    // Option + Padding
} ip_header;

typedef struct ip6_header
{
    uint32_t verpf;
    uint16_t payloadLen;
    uint8_t nextHdr;
    uint8_t hopLimit;
    uint16_t source[8];
    uint16_t dest[8];
} ip6_header;

typedef struct tcp_header
{
  uint16_t    sport;          // Source port
  uint16_t    dport;          // Destination port
  uint32_t    seqno;
  uint32_t    ackno;
  uint8_t     len;            // actual TCP len * 4
  uint8_t     flags;          // Checksum
  uint16_t    windowSize;
  uint16_t    checksum;
  uint16_t    zero;
  uint8_t     options[12];
} tcp_header;

typedef struct udp_header
{
  uint16_t       sport;    // Source port
  uint16_t       dport;    // Destination port
  uint16_t       len;    // Datagram length
  uint16_t       crc;    // Checksum
} udp_header;

typedef struct filepcap_pktheader_s
{
  uint32_t  sec;
  uint32_t  usec;
  uint32_t  caplen;  /* length of portion present */
  uint32_t   len;  /* length this packet (off wire) */
  
} filepcap_pktheader;

void usage();

#ifdef WIN32
void dispatcher_handler(u_char *temp1, 
            const struct pcap_pkthdr *pktheader, 
            const u_char *pktdata)
{
  u_int i=0;
  
  /* Fill the queue with the packets from the file */
  if(pcap_sendqueue_queue(squeue, pktheader, pktdata) == -1)
  {
    fprintf( stderr, "Warning: packet buffer too small, not all the packets will be sent.\n");;
  }
}
#endif

#define MAX_SLEEP_TIME 1000

int packetReady = 0;
char* savepacket = NULL;
struct pcap_pkthdr saveHeader;

static struct timeval lasttv;

static uint16_t 
checksum( uint8_t* p, int len )
{
  uint32_t sum = 0;  /* assume 32 bit long, 16 bit short */

  for( sum = 0; len > 1; len -= 2 )
  {
    sum += ntohs( *(uint16_t *) p );
    if( sum & 0x80000000 )   /* if high order bit set, fold */
    {
      sum = (sum & 0xFFFF) + (sum >> 16);
    }
    p += 2;
  }
  if( len )       /* take care of left over byte */
  {
    sum += *p;
  }
  for( ; sum >> 16; )
  {
    sum = (sum & 0xFFFF) + (sum >> 16);
  }
  return(( uint16_t )  ~sum );
}

static int
translateIP4to6( int mhlen, ip_header* ih, char** ptr, int* len)
{
    int ihlen = 4 * (ih->ver_ihl & 0xF);
    int retval = 0;
    static uint8_t* tbuf = NULL;
    static uint16_t baseip6[8] = { 0, 0, 0, 0, 0, 0xFFFF, 0, 0 };
    static uint16_t mcip6[8] = { 0x2FF, 0, 0, 0, 0, 0, 0, 0 };

    if (NULL == tbuf)
    {
        tbuf = calloc(65536, 1);
    }
    if (tbuf)
    {
        int i = 0;
        int payloadLen = ntohs(ih->tlen) - ihlen;
        uint32_t x = 0;
        ip6_header* ih6 = (ip6_header*)&tbuf[mhlen];

        memcpy(tbuf, *ptr, mhlen);
        tbuf[mhlen - 2] = 0x86;
        tbuf[mhlen - 1] = 0xDD;

        ih6->verpf = 0x60;
        ih6->nextHdr = ih->proto;
        ih6->payloadLen = htons(payloadLen);
        ih6->hopLimit = ih->ttl;
        memcpy(ih6->source, baseip6, sizeof(baseip6));
        memcpy(&ih6->source[6], ih->saddr.byte, sizeof(ih->saddr));

        // Check for MC dest IP
        if ((ih->daddr.byte[0] >= 224) && (ih->daddr.byte[0] <= 239))
        {
            memcpy(ih6->dest, mcip6, sizeof(mcip6));
        }
        else
        {
            memcpy(ih6->dest, baseip6, sizeof(baseip6));
        }
        memcpy(&ih6->dest[6], ih->daddr.byte, sizeof(ih->daddr));

        memcpy(&ih6[1], ((uint8_t*)ih) + ihlen, payloadLen);

        *ptr = tbuf;
        *len += 40 - ihlen;
        
        switch(ih->proto)
        {
        case 6: // TCP
            {
                // Have to recalcuate the TCP checksum since IP6 header doesn't
                // contain a checksum
                tcp_header* th = (tcp_header*)&ih6[1];
                int thlen = th->len >> 2;
                int tcplen = ntohs(ih->tlen) - ihlen;
                uint8_t* pdata = (uint8_t*)th;

                th->checksum = 0; // for now

                for (i = 0; i < 8; i++)
                {
                    x += ntohs(ih6->source[i]);
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                    x += ntohs(ih6->dest[i]);
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                }
                x += 6;
                x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                x += tcplen;
                x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                for (i = 0; i < tcplen - 1; i += 2)
                {
                    x += pdata[i] << 8;
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                    x += pdata[1 + i];
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                }
                if (0 != tcplen % 2)
                {
                    x += pdata[tcplen - 1] << 8;
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                }
                x ^= 0xFFFF;
                th->checksum = htons(x);
            }
            break;
        case 17: // UDP
            {
                udp_header* uh = (udp_header*)&ih6[1];
                uint8_t* pdata = (uint8_t*)uh;
                uint16_t ulen = ntohs(uh->len);

                uh->crc = 0;

                for (i = 0; i < 8; i++)
                {
                    x += ntohs(ih6->source[i]);
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                    x += ntohs(ih6->dest[i]);
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                }
                x += 17;
                x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                x += ulen;
                x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                for (i = 0; i < ulen - 1; i += 2)
                {
                    x += pdata[i] << 8;
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                    x += pdata[1 + i];
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                }
                if (0 != ulen % 2)
                {
                    x += pdata[ulen - 1] << 8;
                    x += (x >= 0x10000) ? 0xFFFF0001 : 0;
                }
                x ^= 0xFFFF;
                uh->crc = htons(x);
            }
            break;
        }
    }
    else
    {
        retval = -1;
    }
    return(retval);
}

static void
handlePacket( const struct pcap_pkthdr *pktheader, 
            const u_char *pktdata)
{
  char* ptr = ( char* ) pktdata;
  int ignore = 0;
  unsigned len = pktheader->len;
  static char buf[ 65536 ];

  counter++;

  if( vlan )
  {
    mac_header_vlan* mhv = ( mac_header_vlan* ) buf;

    memmove( buf, pktdata, 12 );
    
    mhv->tpid = htons( 0x8100 );
    mhv->bits = htons( vlan );

    memmove( & buf[ 16 ], & pktdata[ 12 ], len - 12 );

    ptr = buf;
    len += 4;
  }
  else if( vlanSpecified )
  {
    mac_header_vlan* mhv = (mac_header_vlan*) pktdata;

    if( 0x8100 == ntohs( mhv->tpid ))
    {
      // If there is a VLAN tag and vlan=0, get rid of the tag
      memmove( buf, pktdata, 12 );
      memmove( & buf[ 12 ], & pktdata[ 16 ], len - 16 );
      ptr = buf;
      len -= 4;
    }
  }
  if( ploss )
  {
      if (ploss < 1)
      {
          double d = rand() & 0x7FFF;

          if(( d / 0x7FFF ) < ploss)
          {
              ignore = 1;
          }
      }
      else 
      {
          ignore = 0 == (counter % (unsigned long long)ploss);
      }
  }
  else if( pswap && ! ignore )
  {
    if( ! packetReady )
    {
      double d = rand() & 0x7FFF;

      if(( d / 0x7FFF ) > pswap ) 
      {
        pcap_sendpacket( outdesc, ptr, truncateLen ? ( truncateLen < len ? truncateLen : len ) : len );
      }
      else
      {
        memcpy( & saveHeader, pktheader, sizeof( saveHeader ));
        savepacket = savepacket ? realloc( savepacket, pktheader->len ) : calloc( pktheader->len, 1 );
        memcpy( savepacket, pktdata, pktheader->len );
        packetReady = 1;
      }
    }
    else
    {
      pcap_sendpacket( outdesc, ptr, truncateLen ? ( truncateLen < len ? truncateLen : len ) : len );
      pcap_sendpacket( outdesc, savepacket, 
        truncateLen ? ( truncateLen < saveHeader.len ? truncateLen : saveHeader.len ) : saveHeader.len );
      packetReady = 0;
    }
  }
  else if( ! ignore )
  {
    char* eos = NULL;
    ip_header* ih = ( ip_header* ) & ptr[ 14 ];
    int mhlen = 14;
    int ihlen = 4 * (0xF & ih->ver_ihl);
    mac_header_vlan* mhv = ( mac_header_vlan* ) ptr;

    // Check if the mac header has a VLAN tag in it and if so,
    // adjust the IP header pointer.
    if( 0x8100 == ntohs( mhv->tpid ))
    {
      ih = ( ip_header* )(( uint8_t* ) ih + 4 );
    }
    if( sequenceURICount && ( 6 == ih->proto ))
    {
      int ip_len = ( ih->ver_ihl & 0xf ) * 4;
      tcp_header* th = (tcp_header *) ((uint8_t*) ih + ip_len);
      int thlen = th->len >> 2;
      int tcplen = ntohs( ih->tlen ) - ip_len - thlen;

      if( tcplen )
      {
        char* pURI = ( uint8_t* ) th + thlen;

        if(( 0 == strncmp( pURI, "GET /", 5 )) ||
					( 0 == strncmp( pURI, "PUT /", 5 )) ||
					( 0 == strncmp( pURI, "POST /", 6 )))
        {
          if( eos = strchr( & pURI[ 5 ], ' ' ))
          {
            char seqbuf[ 16 ];
#ifdef WIN32
            int x = sprintf_s( seqbuf, sizeof( seqbuf ),
#else
            int x = sprintf( seqbuf, 
#endif
              "%u/", sequenceURIStart + sequenceURIOffset++ );

            sequenceURIOffset %= sequenceURICount;

            if(( x + 5 + 5 ) < ( eos - pURI ))
            {
              memcpy( & pURI[ 5 ], seqbuf, x );

              //fprintf( stderr, "Made URI %.*s\n", eos - pURI, pURI );
            }
          }
        }
      }
    }
    if( sequenceIP )
    {
      int isFromClient = 0;
      int isFromDestination = 0;
      int seqIP = 0;
      uint32_t srcip = ntohl( *( uint32_t*) ih->saddr.byte );
      uint32_t dstip = ntohl( *( uint32_t*) ih->daddr.byte );

      if(( 6 == ih->proto ) && morphClientOnly )
      {
        tcp_header* th = ( tcp_header* ) & (( char* ) ih )[ ihlen ];

        // Could lookup the server port based on an array of bitmaps
        // But for now just hardcode to 80 or 443
        switch( ntohs( th->dport ))
        {
        case 80:
        case 443:
          srcip += sequenceStart;
          isFromClient = 1;
          break;
        default:
          dstip += sequenceStart;
          break;
        }
      }
      else if(( 6 == ih->proto ) && morphDestinationOnly )
      {
        tcp_header* th = (tcp_header*)&((char*)ih)[ihlen];

        // Could lookup the server port based on an array of bitmaps
        // But for now just hardcode to 80 or 443
        switch( ntohs( th->dport ))
        {
        case 80:
        case 443:
          dstip += sequenceStart;
          break;
        default:
          srcip += sequenceStart;
          isFromDestination = 1;
          break;
        }
      }
      else
      {
        srcip += sequenceStart;
        dstip += sequenceStart;
      }
      for( seqIP = 0; seqIP < sequenceCount; seqIP++ )
      {
        ih->saddr.byte[ 3 ] = 0xFF & srcip;
        ih->saddr.byte[ 2 ] = 0xFF & ( srcip >> 8 );
        ih->saddr.byte[ 1 ] = 0xFF & ( srcip >> 16 );
        ih->saddr.byte[ 0 ] = 0xFF & ( srcip >> 24 );
        ih->daddr.byte[ 3 ] = 0xFF & dstip;
        ih->daddr.byte[ 2 ] = 0xFF & ( dstip >> 8 );
        ih->daddr.byte[ 1 ] = 0xFF & ( dstip >> 16 );
        ih->daddr.byte[ 0 ] = 0xFF & ( dstip >> 24 );
        
        if( ! optimize )
        {
          ih->crc = 0;
          ih->crc = htons( checksum(( uint8_t* ) ih, ( ih->ver_ihl & 0xF ) << 2 ));
        }
        if( translateTo6 && ( 0x40 == ( ih->ver_ihl & 0xF0 )))
        {
            // Have to reset len for morphing to work
            len = pktheader->len;

            translateIP4to6(mhlen, ih, &ptr, &len);
        }
        while( -1 == pcap_sendpacket( outdesc, ptr, truncateLen ? ( truncateLen < len ? truncateLen : len ) : len ))
        {
          fprintf( stderr, "pcap_sendpacket() failed: %s\n", pcap_geterr( outdesc ));
          if( ! aggressive )
          {
            break;
          }  
        }
        if( morphClientOnly )
        {
          if( isFromClient )
          {
            srcip++;
          }
          else
          {
            dstip++;
          }
        }
        else if( morphDestinationOnly )
        {
          if( isFromDestination )
          {
            srcip++;
          }
          else
          {
            dstip++;
          }
        }
        else
        {
          srcip++;
          dstip++;
        }
      }
    }
    else
    {
        if (translateTo6 && (0x40 == (ih->ver_ihl & 0xF0)))
        {
            translateIP4to6(mhlen, ih, &ptr, &len);
        }
        while( -1 == pcap_sendpacket( outdesc, ptr, truncateLen ? ( truncateLen < len ? truncateLen : len ) : len ))
        {
    	    fprintf( stderr, "pcap_sendpacket() failed: %s\n", pcap_geterr( outdesc ));
	        if( ! aggressive )
	        {
	            break;
	        }  
        }
    }
  }
}

static void 
packet_handler( u_char *temp1, 
            const struct pcap_pkthdr *pktheader, 
            const u_char *pktdata)
{
  long long x = 0;
  unsigned long long now = 0;
  static int sock = 0;
  static struct timeval starttv;
  static long long totalDiff = 0;
#ifdef WIN32
  static unsigned long long perfFreq = 0;
  static unsigned long long startTime = 0;
#else
  static struct timeval startTime;
#endif
  static unsigned long pktCount = 0;

  pktCount++;

  if( 0 == sock )
  {
    sock = socket( AF_INET, SOCK_DGRAM, 0 );
  }
  if( bursting )
  {
#ifdef WIN32
    if( lasttv.tv_sec )
    {  
      totalDiff = pktheader->ts.tv_sec;
      totalDiff -= starttv.tv_sec;
      totalDiff *= 1000000L;
      totalDiff += pktheader->ts.tv_usec;
      totalDiff -= starttv.tv_usec;

      for( ;; )
      {
        QueryPerformanceCounter(( union _LARGE_INTEGER* ) & now );

        if( now < startTime )
        {
          startTime = now;
          starttv = pktheader->ts;
          break;
        }
        else
        {
          x = now;
          x -= startTime;
          x *= 1000000L;
          x /= perfFreq;

          if( x > totalDiff )
          {
            break;
          }
          else
          {
            totalDiff -= x;
            totalDiff = ( unsigned long ) ( totalDiff / bursting );

            if( totalDiff )
            {
              fd_set fdin;
              struct timeval delay;

              FD_ZERO( & fdin );
              FD_SET( sock, & fdin );
              delay.tv_sec = ( unsigned long )( totalDiff / 1000000L );
              delay.tv_usec = ( unsigned long )( totalDiff % 1000000L );

              select( 1 + sock, NULL, NULL, & fdin, & delay );
            }
            else
            {
              break;
            }
          }
        }
      }
    }
    else
    {
      QueryPerformanceFrequency(( union _LARGE_INTEGER* ) & perfFreq );
      QueryPerformanceCounter(( union _LARGE_INTEGER* ) & startTime );
      starttv = pktheader->ts;
    }
#else
    if( lasttv.tv_sec )
    {  
      totalDiff = pktheader->ts.tv_sec;
      totalDiff -= starttv.tv_sec;
      totalDiff *= 1000000L;
      totalDiff += pktheader->ts.tv_usec;
      totalDiff -= starttv.tv_usec;

      totalDiff /= bursting;

      for( ;; )
      {
        struct timeval now;

        gettimeofday( & now, NULL );

        if(( now.tv_sec < startTime.tv_sec ) ||
          (( now.tv_sec == startTime.tv_sec ) &&
          ( now.tv_usec < startTime.tv_usec )))
        {
          startTime = now;
          starttv = pktheader->ts;
          break;
        }
        else
        {
          x = now.tv_sec;
          x -= startTime.tv_sec;
          x *= 1000000L;
          x += now.tv_usec;
          x -= startTime.tv_usec;

          //fprintf( stderr, "Delay: %llu %llu\n", totalDiff, x );

          if( x > totalDiff )
          {
            break;
          }
          else
          {
            totalDiff -= x;

            if( totalDiff )
            {
              fd_set fdin;
              struct timeval delay;

              FD_ZERO( & fdin );
              FD_SET( sock, & fdin );
              delay.tv_sec = ( unsigned long )( totalDiff / 1000000L );
              delay.tv_usec = ( unsigned long )( totalDiff % 1000000L );

              select( 1 + sock, NULL, NULL, & fdin, & delay );
            }
            else
            {
              break;
            }
          }
        }
      }
    }
    else
    {
      gettimeofday( & startTime, NULL );
      starttv = pktheader->ts;
    }
#endif
  }
  if( pktheader->len <= mtu )
  {
    // This is the default and original behaviour if there are no jumbo frames
    handlePacket( pktheader, pktdata );
  }
  else
  {
    int i = 0;
    int ok = 1;
    int macBytes = sizeof( mac_header );
    int ipBytes = sizeof( ip_header );
    ip_header* ih = NULL;
    mac_header* mh = ( mac_header* ) pktdata;

    // Allow for 5 VLAN or MPLS headers
    // But not supportnig IP6 for jumbo frames (yet)
    for( i = 0; ( i < 5 ) && ! ih ; i++ )
    {
      switch( mh->type )
      {
      case 0x8: //IP4
        ih = ( ip_header* ) & mh[ 1 ];
        break;
      case 0xdd86: // IP6
        // Not implemented yet
        break;
      default:
        mh = ( mac_header* )& mh->dst[ 4 ]; // Adjust to skip over the VLAN tag
	macBytes += 4;
        // This invalidates mh but it is not used further
        break;
      }
    }
    if( ih )
    {
      int ihlen = 4 * ( 0xF & ih->ver_ihl );
      int headerBytes = macBytes + ipBytes;
      tcp_header* th = NULL;
      udp_header* uh = NULL;
      static uint8_t* header = NULL;
      static uint8_t* localbuf = NULL;
      
      if( ! header )
      {
        header = malloc( 128 );
        localbuf = malloc( 65535 );
      }
      if( ok = (( header != NULL ) && ( localbuf != NULL )))
      {
        memcpy( header, pktdata, 128 );
        memcpy( localbuf, pktdata, pktheader->caplen );

        //Reposition the ih pointer to point into the header buffer
        ih = ( ip_header* )( header + ((( uint8_t* )ih ) - pktdata ));

        switch( ih->proto )
        {
        case 6: // TCP
          th = ( tcp_header* ) & (( char* ) ih )[ ihlen ];
          headerBytes += th->len >> 2;
          break;
        case 17: // UDP
          uh = ( udp_header* ) & (( char* ) ih )[ ihlen ];      
          headerBytes += sizeof( udp_header );
          break;
        default:
          // Don't forward other protocols
          ok = 0;
          break;
        }      
        if( mtu < ( 2 * headerBytes ))
        {
          fprintf( stderr, "MTU is set too small(%u) relative to headerBytes(%u) for packetlen(%u)\n", 
            mtu, headerBytes, pktheader->len );
          ok = 0;
        }
      }
      if( ok  )
      {
        int bytes = mtu - headerBytes;
        int handledBytes = 0;
        int totalBytes = pktheader->len - headerBytes;
        uint32_t seqno = ntohl( th->seqno );
        struct pcap_pkthdr mypktheader = *pktheader;

        mypktheader.caplen = mypktheader.len = mtu;

        ih->tlen = htons( bytes + headerBytes - macBytes );
        if( uh )
        {
          uh->len = htons( bytes );
        }
        for( handledBytes = 0; handledBytes < totalBytes; handledBytes += bytes )
        {
          int remainder = totalBytes - handledBytes;

          if( th )
          {
            th->seqno = htonl( handledBytes + seqno );
          }
          if( mtu >= ( remainder + headerBytes ))
          {
            bytes = remainder;
            mypktheader.caplen = mypktheader.len = bytes + headerBytes;
            ih->tlen = htons( bytes + headerBytes - macBytes );
            if( uh )
            {
              uh->len = htons( bytes );
            }
          }
          // Copy in the modified header at the appropriate spot in the
          // localbuf so that we can just send it from there.
          memcpy( & localbuf[ handledBytes ], header, headerBytes );
          handlePacket( & mypktheader, & localbuf[ handledBytes ]);
        }
      }
    }
  }
  lasttv = pktheader->ts;
}

static void 
printUsage()
{
  char error[PCAP_ERRBUF_SIZE];
  int i = 0;
  pcap_if_t *alldevs = NULL;
  pcap_if_t *d = NULL;
  
  fprintf( stderr, "Sendcap, sends a libpcap/tcpdump capture file to the net.\n");
  fprintf( stderr, "Usage:\n");
  fprintf( stderr, "\t sendcap -f filename -i adapter [-a][-b rate][-l 0.001][-o][-r][-s 0.001][-u [M:]N][-v vlanid][-x [M:]N|-D [M:]N|-S [M:]N][-M mtu]\n");
  fprintf( stderr, "Parameters:\n");
  fprintf( stderr, "-f file_name.pcap: the name of the dump file that will be sent.\n");
  fprintf( stderr, "-i adaptor: the number or name of the device to use.\n");
  fprintf( stderr, "-a if present, retries pcap_sendpacket() until it succeeds\n" );
  fprintf( stderr, "-b rate: if present, forces the packets to be sent at the rate multiplier specified (10->10x, 0.1=>1/10\n" );
  fprintf( stderr, "-c count: if present, limits repetition to count times\n" );
  fprintf( stderr, "-l probability: sets the probability of packet loss if <1 otherwise count between lost packets\n" );
  fprintf( stderr, "-m send from memory(default off)\n" );
  fprintf( stderr, "-o turns off some CRC calculations for better performance while morphing\n" );
  fprintf( stderr, "-p set pause seonds (default 0) for file repetition\n" );
  fprintf( stderr, "-r if present, forces the file to repeat indefinitely\n" );
  fprintf( stderr, "-s probability: sets the probability of packet swapping\n" );
  fprintf( stderr, "-t trunclen: if present, truncate outgoing packets at trunclen\n" );
  fprintf( stderr, "-u [M:]N if present, morphs URI's across N different roots with optional offset M\n" );
  fprintf( stderr, "-v if present, tags the packets as on the specified VLAN\n" );
  fprintf( stderr, "-x [1.1.1.1[:N]|M[:N]] if present, sends multiple copies morphed N times with optional offset M\n" );
  fprintf( stderr, "\tthe arg can start with an IP(1.1.1.1) or partial IP(1.1) which is interpreted as an octet offset\n" );
  fprintf( stderr, "-D [M:]N if present, sends multiple copies with the destIP morphed N times with optional offset M\n" );
  fprintf( stderr, "-S [M:]N if present, sends multiple copies with the clientIP morphed N times with optional offset M\n" );
  fprintf( stderr, "-M mtu if present, set the mtu for packet sending (default 1514)\n" );
  fprintf( stderr, "-6 if present, forces all IP4 traffic to be translated to IP6\n" );
  fprintf( stderr, "Interfaces:\n" );
  /* Retrieve the device list */
  if( pcap_findalldevs( & alldevs, error ) == -1 )
  {
    fprintf( stderr, "Error in pcap_findalldevs: %s\n", error );
    fprintf( stderr, "Ensure that Winpcap 4.0.2 or later is installed\n" );
    exit( -1 );
  }
  if( NULL == alldevs )
  {
    fprintf( stderr, "The network layer may not be ready yet or you may not have \n" );
    fprintf( stderr, "privilege to access the network - waiting to Retry...\n" );
    exit( -1 );
  }
  /* Print the list */
  for( i = 0, d = alldevs; d; d = d->next )
  {
    if( ! quiet )
    {
      fprintf( stderr, "%d. %s %s\n", ++i, d->name, d->description ? d->description : "" );
    }
  }
  exit(0);
}

#ifdef WIN32
char* optarg;

static int
getopt( int argc, char** argv, char* opts )
{
  int retval = 0;
  static int argindex = 1;
  static int nextindex = 2;
  static int optindex = 0;

  for( optarg = NULL; ( argindex < argc ) && ! retval; )
  {
    char* arg = argv[ argindex ];
    char* p = NULL;
    int opt = arg[ optindex ];

    switch( opt )
    {
    case '\0':
      optindex = 0;
      argindex = nextindex++;
      break;
    case '-':
      if( optindex )
      {
        retval = -1;
        break;
      }
      opt = arg[ ++optindex ];
      // fall through
    default:
      if( p = strchr( opts, opt ))
      {
        if( *++p == ':' )
        {
          if( nextindex < argc )
          {
            optarg = argv[ nextindex++ ];
            retval = opt;
          }
          else
          {
            retval = -1;
          }
        }
        else
        {
          retval = opt;
        }
        optindex++;
      }
      else
      {
        retval = -1;
      }
      break;
    }
  }
  if( ! retval )
  {
    retval = -1;
  }
  return( retval );
}
#endif // WIN32

int 
main(int argc, char **argv) 
{
  char error[PCAP_ERRBUF_SIZE];
  char* filename = NULL;
  int opt = 0;
  int retval = 0;
  long long caplen = 0;
  pcap_t *indesc;
  FILE *capfile;

  fprintf( stderr, "Sendcap Version 1.19\n" );

  for( ; -1 != ( opt = getopt( argc, argv, "ab:c:f:i:l:mop:qrs:t:u:v:x:D:M:S:X:6" )); )
  {
    char* p = NULL;

    switch( opt ) 
    {
    case 'a':
      aggressive = 1;
      fprintf( stderr, "Aggressive send set to %d\n", aggressive );
      break;
    case 'b':
      bursting = atof( optarg );
      fprintf( stderr, "Bursting set to %g\n", bursting );
      break;
    case 'c':
      count = atoi( optarg );
      fprintf( stderr, "Repeat count set to %u\n", count );
      break;
    case 'f':
      filename = optarg;
      fprintf( stderr, "Filename set to %s\n", filename );
      break;
    case 'i':
      interfNumber = atoi( interf = optarg );
      fprintf( stderr, "Select interface: %s\n", interf );
      break;
    case 'l':
      ploss = atof( optarg );
      fprintf( stderr, "Probability of loss set to %g\n", ploss );
      break;
    case 'm':
      fprintf( stderr, "Setting send from memory on\n" );
      sendFromMemory = 1;
      break;
    case 'M':
      mtu = atoi( optarg );
      fprintf( stderr, "Setting mtu to %u\n", mtu );
      break;
    case 'o':
      fprintf( stderr, "Setting optimize on\n" );
      optimize = 1;
      break;
    case 'p':
      pauseSeconds = atoi( optarg );
      fprintf( stderr, "Pause seconds set to %u\n", pauseSeconds );
      break;
    case 'q':
      quiet = 1;
      fprintf( stderr, "Quiet set ON\n" );
      break;
    case 'r':
      repeat = 1;
      fprintf( stderr, "Repeat set ON\n" );
      break;
    case 's':
      pswap = atof( optarg );
      fprintf( stderr, "Probability of swap set to %g\n", pswap );
      break;
    case 't':
      truncateLen = atol( optarg );
      fprintf( stderr, "Packet truncation set to %u\n", truncateLen );
      break;
    case 'u':
      {
        char* p = strchr( optarg, ':' );

        if( p )
        {
          sequenceURIStart = atoi( optarg );
          sequenceURICount = atoi( ++p );
        }
        else
        {
          sequenceURIStart = 0;
          sequenceURICount = atoi( optarg );
        }
        fprintf( stderr, "Turned on URI sequencing to %u:%u\n", 
          sequenceURIStart, sequenceURICount );
      }
      break;
    case 'v':
      vlan = atoi( optarg );
      vlanSpecified = 1;
      fprintf( stderr, "Vlan tag ID set to %u\n", vlan );
      break;
    case 'D':
      morphDestinationOnly = 1;
      fprintf( stderr, "Morphing Destination IP's only\n" );
      fprintf( stderr, "Note that this only works for requests to port 80 or 443\n" );
      // fall through
    case 'S':
    case 'X':
      if( opt != 'D' )
      {
        morphClientOnly = 1;
        fprintf( stderr, "Morphing Client IP's only\n" );
        fprintf( stderr, "Note that this only works for requests to port 80 or 443\n" );
      }
      // fall through
    case 'x':
      {
        char* p = strchr( optarg, ':' );
				char* q = strchr( optarg, '.' );
				
				sequenceIP = 1;

				if( q && ((q < p) || !p))
				{
					sequenceStart = atoi( optarg ) << 8;
					sequenceStart += atoi( ++q );

					if( q = strchr( q, '.' ))
					{
						sequenceStart <<= 8;
						sequenceStart += atoi( ++q );

						if( q = strchr( q, '.' ))
						{
							sequenceStart <<= 8;
							sequenceStart += atoi( ++q );
						}
					}
					if( p )
					{
						sequenceCount = atoi( ++p );
					}
					else
					{
						sequenceCount = 1;
					}
				}
				else
				{
					sequenceStart = atoi( optarg );
					if( p )
					{
						sequenceCount = atoi( ++p );
					}
					else
					{
						sequenceCount = sequenceStart;
						sequenceStart = 0;
					}
				}
				fprintf( stderr, "Turned on IP morphing to %s\n", optarg );
			}
      break;
    case '6':
        translateTo6 = 1;
        fprintf(stderr, "Translating to IP6\n");
        break;
    default:
      printUsage();
      break;
    }
  }
  if( filename == NULL )
  {
    printUsage();
  }
  else 
  {
    if( 0 == strcmp( filename, "-" ))
    {
      capfile = stdin;
    }
    else
    {
#ifdef WIN32
      fopen_s( & capfile, filename, "rb" );
#else
      capfile = fopen( filename, "rb" );
#endif
    }
    if( ! capfile )
    {
      fprintf( stderr, "Capture file not found!\n" );
    }
    else
    {
      char* p = NULL;
      int i = 0;
      pcap_if_t *alldevs = NULL;
      pcap_if_t *d = NULL;
      char* memBuffer = NULL;

      if( strcmp( filename, "-" ))
      {
        /* Retrieve the length of the capture file */
        fseek( capfile, 0, SEEK_END );
        caplen = ftell( capfile );
        
        if( sendFromMemory )
        {
          rewind( capfile );

          if(( caplen >= 0x100000000LL ) || ( NULL == ( memBuffer = malloc(( size_t ) caplen ))))
          {
            fprintf( stderr, "Not enough memory to allocate memory buffer\n" );
            sendFromMemory = 0;
          }
          else
          {
            int read = 0;
            for( ; read < caplen; )
            {
              read += fread( & memBuffer[ read ], 1, (( size_t ) caplen ) - read, capfile );
            }
          }
        }
        fclose( capfile );
      }
      /* Chek if the timestamps must be respected */
      if( 0 == bursting )
      {
        synchronize = FALSE;
      }
      else
      {
        synchronize = TRUE;
#ifdef WIN32
        if( ! SetPriorityClass( GetCurrentProcess(), REALTIME_PRIORITY_CLASS ))
        {
          fprintf( stderr, "Failed to set REALTIME_PRIORITY_CLASS\n" );
        }
        if( ! SetThreadPriority( GetCurrentThread(), THREAD_PRIORITY_TIME_CRITICAL ))
        {
          fprintf( stderr, "Failed to set THREAD_PRIORITY_TIME_CRITICAL\n" );       
        }
#endif
      }
      /* Retrieve the device list */
      if( pcap_findalldevs( & alldevs, error ) == -1 )
      {
        fprintf( stderr, "Error in pcap_findalldevs: %s\n", error );
        fprintf( stderr, "Ensure that Winpcap 4.0.2 or later is installed\n" );
        exit( -1 );
      }
      if( NULL == alldevs )
      {
        fprintf( stderr, "The network layer may not be ready yet or you may not have \n" );
        fprintf( stderr, "privilege to access the network - waiting to Retry...\n" );
        exit( -1 );
      }
      /* Print the list */
      for( i = 0, d = alldevs; d; d = d->next )
      {
        if( ! quiet )
        {
          fprintf( stderr, "%d\t%s\t%s\n", ++i, d->name, d->description ? d->description : "" );
        }
      }
      if( interfNumber )
      {
        for( i = 0, d = alldevs; d; d = d->next )
        {
          if( interfNumber == ++i )
          {
            break;
          }
        }
      }
      /* Check for interf specified as text */
      else if( interf && ( 0 == interfNumber ))
      {
        for( i = 0, d = alldevs; d; i++, d = d->next )
        {
          if(( d->name && ( 0 == strcmp( d->name, interf ))) || 
            ( d->description && ( 0 == strcmp( d->description, interf ))))
          {
            interfNumber = 1 + i;
            break;
          }
        }
      }
      if( 0 == interfNumber )
      {
        /* Check for first Ethernet-like interface */
        for( i = 0, d = alldevs; d; i++, d = d->next )
        {
          if( d->description )
          {
            if( strstr( d->description, "thernet" ))
            {
              if( 0 == interfNumber )
              {
                interfNumber = 1 + i;
                break;
              }
            }
          }
        }
      }
      if( 0 == interfNumber )
      {
        fprintf( stderr, "Interface not specified or found\n" );
        exit( -1 );
      }
      if( d )
      {
        if( ! quiet )
        {
          fprintf( stderr, "Using interface#%u %s - %s\n", interfNumber, 
            d->name ? d->name : "no name", 
            d->description ? d->description : "no description");
        }
        /* Open the output adapter */
        if((outdesc = pcap_open_live( d->name, 65535, 1, 1000, error) ) == NULL)
        {
          fprintf(stderr,"\nError opening adapter: %s\n", error);
          exit( -1 );
        }
        for( ;; )
        {
          if( memBuffer )
          {
            uint32_t c = 0;
            struct pcap_file_header* pfh = 
              ( struct pcap_file_header* ) memBuffer;
            p = memBuffer + sizeof( *pfh );

            for( c = 0; p < & memBuffer[ caplen ]; c++ )
            {
              if( p )
              {
                const filepcap_pktheader *filepktheader = ( const filepcap_pktheader* ) p;
                struct pcap_pkthdr pktheader;
                const u_char *pktdata = ( const u_char* )( p += sizeof( filepcap_pktheader ));

                pktheader.ts.tv_sec = filepktheader->sec;
                pktheader.ts.tv_usec = filepktheader->usec;
                pktheader.caplen = filepktheader->caplen;
                pktheader.len = filepktheader->len;

                //fprintf( stderr, "pcap_pkthdr: %u %u %u %u\n",
                //  pktheader.ts.tv_sec, pktheader.ts.tv_usec,
                //  pktheader.caplen, pktheader.len );

                //fprintf( stderr, "%lX %u\n", pktdata, c );
                packet_handler( NULL, & pktheader, pktdata );

                p += pktheader.caplen;
              }
            }
          }
          else 
          {
            if( strcmp( filename, "-" ))
            {
              /* Open the capture */
              if(( indesc = pcap_open_offline( filename, error )) == NULL)
              {
                fprintf(stderr,"\nError opening the input file: %s\n", error);
                exit( -1 );;
              }
              /* Check the MAC type */
              if( pcap_datalink( indesc ) != pcap_datalink( outdesc ))
              {
                fprintf( stderr, "Warning: the datalink of the capture differs from the one of the selected interface.\n");
              }
#ifdef WIN32
              if( ! synchronize )
              {
                unsigned res = 0;

                /* Allocate a send queue */
                squeue = pcap_sendqueue_alloc(( size_t ) caplen );

                /* read and dispatch packets until EOF is reached */
                pcap_loop( indesc, 0, dispatcher_handler, NULL);

                /* Transmit the queue */

                if(( res = pcap_sendqueue_transmit(outdesc, squeue, synchronize)) < squeue->len)
                {
                  fprintf( stderr, "An error occurred sending the packets: %s. Only %d bytes were sent\n", error, res);
                }
                /* free the send queue */
                pcap_sendqueue_destroy(squeue);
              }
              else
#endif
              {
                /* read and dispatch packets until EOF is reached */
                pcap_loop( indesc, 0, packet_handler, NULL);
              }
              pcap_close( indesc );
            }
#ifdef NOT_READY
            else
            {
              int fails = 0;
              int len = 0;
              unsigned char header[ 24 ];

              // Ignore the global pcap file header
              if( 0 >= ( len = fread( & header, 1, sizeof( header ), capfile )))
              {
                break;
              }
#ifdef NOT_NEEED
              else
              {
                fprintf( stderr, "Read %u bytes of header\n", len );
                for( i = 0; i < len; i++ )
                {
                  fprintf( stderr, "%02.2X ", header[ i ]);
                }
                fprintf( stderr, "\n" );
              }
#endif
              for( fails = 0; fails < 10; )
              {
                int len = 0;
                unsigned char temp = 0;
                struct pcap_pkthdr pktheader;
                unsigned char pktdata[ 2048 ];
                
                if( 0 >= fread( & pktheader, 1, sizeof( pktheader ), capfile ))
                {
                  fails++;
                }
                else
                {
#ifdef NOT_NEEED
                  fprintf( stderr, "Read %u bytes of pktheader\n", len );
                  fprintf( stderr, "Time: %u.%06.6u\n", pktheader.ts.tv_sec,
                    pktheader.ts.tv_usec );
                  fprintf( stderr, "Caplen: %u\n", pktheader.caplen );
                  fprintf( stderr, "len: %u\n", pktheader.len );
#endif
                  if( 0 >= ( len = fread( pktdata, 1, pktheader.caplen, capfile )))
                  {
                    fails++;
                  }
                  else
                  {  
                    fails = 0;
                  }
                }
                if( 0 == fails )
                {
                  packet_handler( NULL, & pktheader, pktdata );
                }
                else
                {
                  int ms = 1000;
                  time_t sec = ms / 1000;
                  long nsec = ( ms % 1000 ) * 1000000;
                  struct timespec req;

                  req.tv_sec = sec;
                  req.tv_nsec = nsec;

                  nanosleep( & req, NULL );
                }
              }
            }
#endif
          }
          if( repeat )
          {
            lasttv.tv_sec = 0;
            
            // Apply the countRepeats check before the pause check
            // If the sendcap is scripted with a count then a pause
            // can be added in the script after the last iteration 
            // if so desired.
            if( count && ( count <= ++countRepeats ))
            {
              exit( 0 );
            }
            if( pauseSeconds )
            {
              if( ! quiet )
              {
                fprintf( stderr, "Pausing for %u seconds\n", pauseSeconds );
              }
#ifdef WIN32
              Sleep( 1000 * pauseSeconds );
#else
              sleep( pauseSeconds );
#endif          
            }
          }
          else
          {
            break;
          }
        }
        pcap_close( outdesc );
      }
      else
      {
        printUsage();
      }
    }
  }
  return( retval );
}
