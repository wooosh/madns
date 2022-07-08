/*******************************************************************************
 *  __  __          _____  _   _  _____                                        *
 * |  \/  |   /\   |  __ \| \ | |/ ____| [M]ini                                *
 * | \  / |  /  \  | |  | |  \| | (___   [A]uthoritative                       *
 * | |\/| | / /\ \ | |  | | . ` |\___ \  [D]omain                              *
 * | |  | |/ ____ \| |__| | |\  |____) | [N]ame                                *
 * |_|  |_/_/    \_\_____/|_| \_|_____/  [S]erver                              *
 *    (c) 2022 wooosh | MIT Licensed                                           *
 *******************************************************************************
 * Features:
 *   > Supports standard zonefiles
 *   > Zero configruation required
 *   > Low resource usage (zero transient allocations)
 *   > Multithreaded
 *   > Small codebase, zero dependencies
 *
 * Use
 *
 * TODO: wildcards
 * TODO: allow binding on a specific IP
 * TODO: threading
 * TODO: $TTL
 * TODO: read TTL values
 * TODO: read class values
 * TODO: finish line based error reporting
 * TODO: finish the first line comment bug
 * TODO: restrict A records to IN class
 * TODO: error responses
 *
 * TODO: investigate all RFCS
 * TODO: testing
 * TODO: escaping
 *
 * Supported Standards:
 * - 1034 [DOMAIN NAMES - CONCEPTS AND FACILITIES]
 * - 1035 [DOMAIN NAMES - IMPLEMENTATION AND SPECIFICATION]
 * - 4343 [Domain Name System (DNS) Case Insensitivity Clarification] 
 */

#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <stddef.h>
#include <netinet/in.h>

/******************************************************************************
 * UTILITIES                                                                  *
 ******************************************************************************/
/* TODO: change to fit naming conventions */
static void Die(const char *msg) {
    fprintf(stderr, "fatal: %s\n", msg);
    exit(EXIT_FAILURE);
}

static void DieErrno(const char *msg) {
  fprintf(stderr, "fatal: %s: %s\n", msg, strerror(errno));
  exit(EXIT_FAILURE);
}

static void *CheckedMalloc(size_t size) {
  void *ptr = malloc(size);
  if (ptr == NULL) Die("allocation failure");
  return ptr;
}

struct Buf {
  char *begin;
  char *c; /* cursor */
  char *end;
};

/* returns false on failure */
static bool BufWrite(struct Buf *b, void *data, size_t len) {
  if (b->c + len >= b->end) return false;
  memcpy(b->c, data, len);
  b->c += len;
  return true;
}

static void TryBufWrite(struct Buf *b, void *data, size_t len,  char *err) {
  if(!BufWrite(b, data, len)) Die(err);
}

/* normalizes a DNS encoded name for case insensivity */ 
static void NormalizeDNSName(char *name) {
  /* according to RFC 4343:
   *   One way to implement this [case insensitvity] rule would be to 
   *   subtract 0x20 from all octets in the inclusive range from 0x61
   *   to 0x7A before comparing octets. */
  while (*name != 0) {
    size_t len = *name;
    name++;
    for (size_t i=0; i<len; i++) {
      if (name[i] >= 0x61 && name[i] <= 0x7A) name[i] -= 0x20;
    }
    name += len;
  } 
}

/******************************************************************************
 * RECORD SET/"DATABASE"                                                      *
 ******************************************************************************/
struct RecordSet {
  struct RecordSetEntry *entries;
  size_t len;
  size_t cap;
} record_set;

struct RecordSetEntry {
  uint16_t record_type;
  char *encoded_record;
  size_t name_len; /* the name begins the encoded record */
  size_t total_len;
  bool wildcard;
};

typedef size_t RecordSetCursor;

static void RecordSetInit(void) {
  record_set.entries = NULL;
  record_set.len = 0;
  record_set.cap = 0;
}

static RecordSetCursor RecordSetCursorNew(void) {return 0;}

static void RecordSetAppend(struct RecordSetEntry ent) {
  record_set.len++;
  if (record_set.len >= record_set.cap) {
    if (record_set.cap == 0) record_set.cap = 1;
    while (record_set.len >= record_set.cap) record_set.cap *= 2;
    record_set.entries = realloc(record_set.entries,
      record_set.cap * sizeof(struct RecordSetEntry));
    if (record_set.entries == NULL) Die("realloc failed");
  }

  record_set.entries[record_set.len-1] = ent;
}

/* expects the name to be normalized beforehand */
/* TODO: handle class, type */
static struct RecordSetEntry *
RecordSetLookup(int type, char *encoded_name, size_t name_len,
                RecordSetCursor *c) {
  for (; *c < record_set.len; *c += 1) {
    struct RecordSetEntry ent = record_set.entries[*c];
    /* TODO: handle wildcards */
    if (ent.name_len == name_len &&
        memcmp(ent.encoded_record, encoded_name, name_len) == 0) {
      *c += 1;
      return record_set.entries + *c - 1;
    }
  }
  return NULL;
}

/******************************************************************************
 * ZONEFILE PARSER                                                            *
 ******************************************************************************/
struct ParserState {
  struct Buf file;
  char *last_owner;
  size_t last_owner_len;
  char *origin;
  size_t origin_len;
  size_t lineno;
  char *filename;
  bool in_parens;
};

#define ERR_RECORD_LEN "attempted to create DNS record larger than 512 bytes"

void ParserError(struct ParserState *s, char *msg) {
    fprintf(stderr, "fatal parser error @ %s:%zu: %s\n", s->filename, s->lineno,
      msg);
    exit(EXIT_FAILURE);
}

/* returns next field within the record */
static char *NextField(struct ParserState *s, size_t *len) {
  // TODO: handle parens and comments
  while (s->file.c < s->file.end
    && (*s->file.c == ' ' || *s->file.c == '\t'))
    s->file.c++;

  char *begin = s->file.c;
  
  while (s->file.c < s->file.end
    && !(*s->file.c == ' ' || *s->file.c == '\t' || *s->file.c == '\n'))
    s->file.c++;
  
  *len = s->file.c - begin;
  if (*len == 0) ParserError(s, "expected more fields");
  return begin;
}

static bool NextRecord(struct ParserState *s) {
  /* TODO: skip blank and comment lines and handle unclosed parens */
  char *line_start = NULL;
  while (s->file.c < s->file.end
    && (*s->file.c == '\t' || *s->file.c == ' ' ||
        *s->file.c == '\n' || *s->file.c == ';')) {
    if (*s->file.c == ';') {
      while (s->file.c < s->file.end && *s->file.c != '\n') s->file.c++;
    } else {
      if (*s->file.c == '\n') line_start = s->file.c + 1;
      s->file.c++;
    }
  }
  if (s->file.c >= s->file.end) return false;
  s->file.c = line_start;
  return true;
}

static uint64_t StrToU64(char *str, char *end) {
  // TODO: error handling for overflow and invalid chars
  uint64_t n = 0;
  while (str != end) {
    n = n*10 + (*str - '0');
    str++;
  }
  return n;
}

static void PopUint(struct ParserState *s, unsigned size, struct Buf *rr) {
  size_t len;
  char *field = NextField(s, &len);

  uint64_t n = StrToU64(field, field+len);
  switch (size) {
    case 1:
      if (n > UINT8_MAX) ParserError(s, "number must be 8 bits or less");
      break;
    case 2:
      if (n > UINT16_MAX) ParserError(s, "number must be 16 bits or less");
      n = htons(n);
      break;
    case 4:
      if (n > UINT32_MAX) ParserError(s, "number must be 32 bits or less");
      n = htonl(n);
      break;
    default: Die("invalid size");
  }

  TryBufWrite(rr, &n, size, ERR_RECORD_LEN);
}

static void PopIPV4Address(struct ParserState *s, struct Buf *rr) {
  size_t len;
  char *field = NextField(s, &len);
  
  char addr[4];
  char *num_start = field;
  char *num_end = field;
  char *end = field + len;
  for (size_t i=0; i<4; i++) {
    if (i<3)  {
      while (num_end != end && *num_end != '.') num_end++;
      if (num_end == end)
        ParserError(s, "unexpected EOF while reading IPv4 address");
    } else num_end = end;

    uint64_t n = StrToU64(num_start, num_end);
    if (n > UINT8_MAX) ParserError(s, "IPv4 address field too large");
    addr[i] = n;  
    
    num_start = num_end + 1;
    num_end = num_start;
  }

  TryBufWrite(rr, addr, 4, ERR_RECORD_LEN);
}

static bool PopStr(struct ParserState *s, struct Buf *rr) {
  /* TODO */
  return false;
}

#define ERR_UNSET_ORIGIN "record is relative to origin, but no origin is known"
static void PopDomain(struct ParserState *s, struct Buf *rr) {
  size_t len;
  char *field = NextField(s, &len);

  char *start = rr->c;

  if (len == 1 && *field == '@') {
    if (s->origin == NULL) ParserError(s, ERR_UNSET_ORIGIN);
    TryBufWrite(rr, s->origin, s->origin_len, ERR_RECORD_LEN);
  }

  size_t running_len = 0;
  for (size_t i=0; i<len; i++) {
    if (running_len >= 64)
      ParserError(s, "DNS labels must be at most 63 bytes");
    if (field[i] == '.') {
      if (i == 0)
        ParserError(s, "each domain label must be at least one character long "
          "(each dot must have at least one label before it)");
      TryBufWrite(rr, &running_len, 1, ERR_RECORD_LEN);
      TryBufWrite(rr, field + i - running_len, running_len, ERR_RECORD_LEN);
      running_len = 0;
    } else {
      running_len++;
    }
  }

  if (running_len > 0) { /* domains that are relative to the origin */
    TryBufWrite(rr, &running_len, 1, ERR_RECORD_LEN);
    TryBufWrite(rr, field + len - running_len, running_len, ERR_RECORD_LEN);
    if (s->origin == NULL) ParserError(s, ERR_UNSET_ORIGIN);
    TryBufWrite(rr, s->origin, s->origin_len, ERR_RECORD_LEN);
  } else {
    TryBufWrite(rr, &(uint8_t){0}, 1, ERR_RECORD_LEN);
  }
  
  if (rr->c - start > 255)
    ParserError(s, "DNS names must be at most 255 bytes");
}

#define RECORD_TYPES \
RECORD_TYPE(A,      1, IPV4_ADDR)\
RECORD_TYPE(NS,     2, DOMAIN)\
RECORD_TYPE(MD,     3, DOMAIN)\
RECORD_TYPE(MF,     4, DOMAIN)\
RECORD_TYPE(CNAME,  5, DOMAIN)\
RECORD_TYPE(SOA,    6, DOMAIN DOMAIN U32 U32 U32 U32 U32)\
RECORD_TYPE(MB,     7, DOMAIN)\
RECORD_TYPE(MG,     8, DOMAIN)\
RECORD_TYPE(MR,     9, DOMAIN)\
/* RECORD_TYPE(NULL,  10, VARLEN)  disallowed in zonefiles */\
/* RECORD_TYPE(WKS,   11, U32 U8 VARLEN)*/\
RECORD_TYPE(PTR,   12, DOMAIN)\
RECORD_TYPE(HINFO, 13, STR STR)\
RECORD_TYPE(MINFO, 14, DOMAIN DOMAIN)\
RECORD_TYPE(MX,    15, U16 DOMAIN)\
RECORD_TYPE(TXT,   16, STR)

#define U8  PopUint(s, 1, rr);
#define U16 PopUint(s, 2, rr);
#define U32 PopUint(s, 4, rr);
#define STR PopStr(s, rr); 
#define IPV4_ADDR PopIPV4Address(s, rr);
#define DOMAIN PopDomain(s, rr);

#define RECORD_TYPE(name, id, fields)\
void Record##name##Pop(struct ParserState *s, struct Buf *rr) {\
  fields\
}

RECORD_TYPES

#undef U8
#undef U16
#undef U32
#undef STR
#undef DOMAIN
#undef RECORD_TYPE

#define RECORD_TYPE(name, id, fields) {#name, id, Record##name##Pop},

struct RecordId {
  char *name;
  uint16_t id;
  void (*parser)(struct ParserState *, struct Buf *);
} record_ids[] = {
  RECORD_TYPES
  {NULL, 0, NULL}
};

#undef RECORD_TYPE

#define RECORD_TYPE(name, id, fields) kRecordType_ ## name = id,

enum {
  RECORD_TYPES
};

#undef RECORD_TYPE

static struct RecordSetEntry ReadRecord(struct ParserState *s) {
  // TODO: wildcards
  char *buf = CheckedMalloc(512);
  struct Buf rr = {.begin = buf, .c = buf, .end = buf+512};
  // TODO: eof checks
  if (*s->file.c == ' ' || *s->file.c == '\t') {
    if(s->last_owner == NULL)
      Die("owner field is empty and no previous owner known");
    TryBufWrite(&rr, s->last_owner, s->last_owner_len, ERR_RECORD_LEN);
  } else {
    PopDomain(s, &rr);
    NormalizeDNSName(rr.begin);
  }
  size_t name_len = rr.c - rr.begin;
  s->last_owner = rr.begin;
  s->last_owner_len = name_len;
  /*
  if (TryPopTTL()) TryPopClass();
  else if (TryPopClass()) TryPopTTL();
  */
  // Pop Type

  size_t len;
  char *type_field = NextField(s, &len);
  // TODO: check that it returned, todo: use bool flag to indicate required
  for (size_t i=0; record_ids[i].name != NULL; i++) {
    if (len == strlen(record_ids[i].name)
        && strncmp(type_field, record_ids[i].name, len) == 0) {
      // TODO: use TryBufWrite
      uint16_t encoded_type_id = htons(record_ids[i].id);
      memcpy(rr.c, &encoded_type_id, 2);
      rr.c += 2;

      uint16_t class = htons(1); // IN TODO: support others
      memcpy(rr.c, &class, 2);
      rr.c += 2;
      
      uint32_t ttl = htonl(3600);
      memcpy(rr.c, &ttl, 4);
      rr.c += 4;

      char *rdlength_field = rr.c;
      rr.c += 2;
      char *rdata_begin = rr.c;

      record_ids[i].parser(s, &rr);

      uint16_t rdlength = htons(rr.c - rdata_begin);
      memcpy(rdlength_field, &rdlength, 2);

      struct RecordSetEntry ent = {
        .record_type = record_ids[i].id,
        .encoded_record = buf,
        .name_len = name_len,
        .total_len = rr.c - rr.begin,
        .wildcard = false
      };

      RecordSetAppend(ent);
      
      return ent;
    }
  }
  Die("unknown record type");
}

static void ReadZoneFile(char *file) {
  struct ParserState s = {
    .file = {.begin = NULL, .c = NULL, .end = NULL},
    .last_owner = NULL,
    .last_owner_len = 0,
    .origin = NULL,
    .origin_len = 0,
    .lineno = 1,
    .filename = file,
    .in_parens = false,
  };
  
  char origin_s[255];
  struct Buf origin_buf = {
    .begin = origin_s,
    .c = origin_s,
    .end = origin_s + 255
  };

  /* load file into memory */
  FILE *f = fopen(file, "rb"); /* TODO: error checking */
  if (f == NULL) Die("unable to open zonefile");
  if (fseek(f, 0, SEEK_END) != 0) Die("unable to seek zonefile");
  size_t len = ftell(f);
  if (len == -1L) DieErrno("unable to get file position");
  s.file.begin = CheckedMalloc(len);
  s.file.c = s.file.begin;
  s.file.end = s.file.begin + len;
  fseek(f, 0, SEEK_SET);
  fread(s.file.begin, 1, len, f);
  fclose(f);

  /* used to enforce the SOA record appearing first in the zonefile */
  bool soa_found = false;

  /* TODO: allow comments and whitespace at beginning of file */
  do {
    if (s.file.c < s.file.end && *s.file.c == '$') {
      size_t len;
      char *field = NextField(&s, &len);
      if (len == strlen("$ORIGIN") && memcmp(field, "$ORIGIN", len) == 0) {
        /* TODO: require the domain to be fully qualified */
        origin_buf.c = origin_buf.begin;
        PopDomain(&s, &origin_buf);
        s.origin = origin_buf.begin;
        s.origin_len = origin_buf.c - origin_buf.begin;
      }
    } else {
      struct RecordSetEntry ent = ReadRecord(&s);
      if (!soa_found) {
        if (ent.record_type != kRecordType_SOA)
          Die("first record in zonefile must be a SOA record");
        soa_found = true;
      }
    }
  } while (NextRecord(&s));
  free(s.file.begin);
}

/******************************************************************************
 * QUERY HANDLING                                                             *
 ******************************************************************************/

static int sockfd;

typedef uint16_t DNSHeaderField;
enum {
  kDNSHeaderField_QR     =   1 << 0,
  kDNSHeaderField_OPCODE = 0xF << 1,
  kDNSHeaderField_AA     =   1 << 5,
  kDNSHeaderField_TC     =   1 << 6,
  kDNSHeaderField_RD     =   1 << 7,
  kDNSHeaderField_RA     =   1 << 8,
  kDNSHeaderField_Z      = 0x7 << 9,
  kDNSHeaderField_RCODE  = 0xF << 12,
  
  kDNSHeaderField_RCODE_Success   = 0 << 12,
  kDNSHeaderField_RCODE_FormatErr = 1 << 12,
  kDNSHeaderField_RCODE_ServFail  = 2 << 12,
  kDNSHeaderField_RCODE_NameErr   = 3 << 12,
  kDNSHeaderField_RCODE_NotImpl   = 4 << 12,
  kDNSHeaderField_RCODE_Refused   = 5 << 12
};


/* macro type definitions */
struct DNSHeader {
  uint16_t id;
  uint16_t flags;
  uint16_t qdcount;
  uint16_t ancount;
  uint16_t nscount;
  uint16_t arcount;
};

void ReplyError(struct DNSHeader header) {
  /* TODO */
}

void ServerLoop(void) {
  char query_s[512];
  struct Buf query = {.begin = query_s, .c = query_s,
                      .end   = query_s+sizeof(query_s)};
  char reply_s[512];
  struct Buf reply = {.begin = reply_s, .c = reply_s,
                      .end   = reply_s+sizeof(reply_s)};

  while (true) {
    query.c = query.begin;
    reply.c = reply.begin;

    socklen_t client_addr_len;
    struct sockaddr_in client_addr;
    int len = recvfrom(sockfd, query.begin, sizeof(query_s), 0,
      (struct sockaddr*) &client_addr, &client_addr_len);
    query.end = query.begin + len;
    
    struct DNSHeader hdr;
    memcpy(&hdr, query.c, sizeof(hdr));
    query.c += sizeof(hdr);

    if (ntohs(hdr.qdcount) != 1) {
      ReplyError(hdr);
      continue;
    }

    /* read question */
    char *name_start = query.c;
    while (query.c <= query.end && *query.c != 0) {
      query.c += *query.c + 1;
    } 
    if (query.c + 1 >= query.end) {
      ReplyError(hdr);
      continue;
    }
    query.c++; /* skip terminating zero */
    size_t name_len = query.c - name_start;
    NormalizeDNSName(name_start);
    uint16_t qtype, qclass;

    if (query.c + 4 > query.end) {
      ReplyError(hdr);
      continue;
    }
    memcpy(&qtype, query.c, 2);
    query.c += 2;
    memcpy(&qclass, query.c, 2);
    query.c += 2;

    qtype = ntohs(qtype);
    qclass = ntohs(qclass);
   
    /* formulate response */
    hdr.flags |= kDNSHeaderField_QR;
    hdr.qdcount = 0;
    hdr.ancount = 0;
    hdr.nscount = 0;
    hdr.arcount = 0;
    /* TODO: bufwrite + handle failure */
    memcpy(reply.c, &hdr, sizeof(hdr));
    reply.c += sizeof(hdr);
   
    RecordSetCursor rc = RecordSetCursorNew();
    struct RecordSetEntry *ent;
    while (true) {
      ent = RecordSetLookup(qtype, name_start, name_len, &rc);
      if (ent == NULL) break;
      /* TODO: handle failure */
      TryBufWrite(&reply, ent->encoded_record, ent->total_len, "pain");
      hdr.nscount++;
    } while (ent != NULL);
   
    hdr.nscount = htons(hdr.nscount); 
    memcpy(reply.begin + offsetof(struct DNSHeader, nscount), &hdr.nscount, 2);

    sendto(sockfd, reply.begin, reply.c - reply.begin, 0, (struct sockaddr *) &client_addr, sizeof(client_addr));
  }
}

/******************************************************************************
 * COMMAND LINE INTERFACE & DRIVER                                            *
 ******************************************************************************/
static void ParseArguments(int argc, char **argv, char **zonefile, int *port) {
  *zonefile = NULL;
  *port = 53;
  for (int i=1; i<argc; i++) {
    if (strncmp(argv[i], "-h", 2) == 0 || strncmp(argv[i], "--h", 3) == 0) {
      fprintf(stderr,
        "%s - micro authoritative domain name server\n"
        "\n"
        "usage:\n"
        "  %s [-port port] <-file zonefile>\n"
        "    serve records from zonefile on the given port (53 is default)\n"
        "  %s -h, %s -help, %s --help\n"
        "    display help information\n",
        argv[0], argv[0], argv[0], argv[0], argv[0]);
      exit(EXIT_SUCCESS);
    } else if (strcmp(argv[i], "-port") == 0) {
      i++;
      if (i >= argc) Die("expected port number following -port");
      
      errno = 0;
      char *endptr;
      *port = (int) strtol(argv[i], &endptr, 10);
      if (errno != 0 || argv[i] == endptr || *endptr != '\0')
        Die("invalid port number given");
    } else if (strcmp(argv[i], "-file") == 0) {
      i++;
      if (i >= argc) Die("expected filename following -file");

      *zonefile = argv[i];
    } else {
      Die("unknown argument");
    }
  }

  if(*zonefile == NULL) Die("zonefile required");
}

static void BindUDPSocket(int port) {
  struct sockaddr_in server_addr;
  memset(&server_addr, 0, sizeof(server_addr));

  server_addr.sin_family      = AF_INET;
  server_addr.sin_port        = htons(port);
  server_addr.sin_addr.s_addr = htonl(INADDR_ANY);

  sockfd = socket(PF_INET, SOCK_DGRAM, 0);
  if (sockfd < 0) DieErrno("failed to create socket");

  int err = bind(sockfd, (struct sockaddr*) &server_addr, sizeof(server_addr));
  if (err < 0) DieErrno("failed to bind socket");
}

int main(int argc, char **argv) {
  char *zonefile;
  int port;

  ParseArguments(argc, argv, &zonefile, &port);
  RecordSetInit();
  ReadZoneFile(zonefile);
  BindUDPSocket(port);

  ServerLoop();

  return EXIT_SUCCESS;
}
