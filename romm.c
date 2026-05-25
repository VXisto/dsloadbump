/*
 * romm.c - RoMM integration for DSLoad v2
 *
 * Implements a minimal HTTP/1.0 client using dswifi9's BSD socket API,
 * a lightweight JSON field extractor (no heap allocations), and an
 * interactive console UI for browsing and downloading ROMs from a local
 * RoMM server.
 */

#include "romm.h"

#include <nds.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>
#include <zlib.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <math.h>


/* ==========================================================================
 * Log file
 * ========================================================================== */

static FILE *log_fp = NULL;

void romm_log_init(void) {
	/* Use "w" (overwrite) so a fresh log is always created/truncated. */
	log_fp = fopen(ROMM_LOG_FILE, "w");
	if (log_fp) {
		setvbuf(log_fp, NULL, _IONBF, 0); /* unbuffered – writes hit card immediately */
		fprintf(log_fp, "=== DSLoad v%s  RoMM session start ===\n",
		        ROMM_VERSION);
		fflush(log_fp);
	} else {
		/* Visible warning so the user knows logging is broken */
		printf("[WARN] Cannot open log file:\n%s\n", ROMM_LOG_FILE);
	}
}

void romm_log_close(void) {
	if (log_fp) {
		fprintf(log_fp, "=== RoMM session end ===\n\n");
		fclose(log_fp);
		log_fp = NULL;
	}
}

void romm_log(const char *fmt, ...) {
	if (!log_fp) return;
	va_list ap;
	va_start(ap, fmt);
	vfprintf(log_fp, fmt, ap);
	va_end(ap);
	fputc('\n', log_fp);
	fflush(log_fp);
}


/* ==========================================================================
 * Config loader
 * ========================================================================== */

int romm_load_config(RommConfig *cfg) {
	memset(cfg, 0, sizeof(*cfg));
	/* Defaults */
	cfg->port = 3000;
	strcpy(cfg->download_dir, "/roms");

	FILE *fp = fopen(ROMM_CONFIG_FILE, "r");
	if (!fp) return 0;

	char line[256];
	while (fgets(line, sizeof(line), fp)) {
		/* Strip trailing whitespace */
		int len = strlen(line);
		while (len > 0 && (line[len-1] == '\n' || line[len-1] == '\r'
		                   || line[len-1] == ' '))
			line[--len] = '\0';
		/* Skip blank lines and comments */
		if (line[0] == '#' || line[0] == '\0') continue;

		char *eq = strchr(line, '=');
		if (!eq) continue;
		*eq = '\0';
		const char *key = line;
		const char *val = eq + 1;

		if      (strcmp(key, "server")       == 0)
			strncpy(cfg->server,       val, sizeof(cfg->server)       - 1);
		else if (strcmp(key, "port")         == 0)
			cfg->port = atoi(val);
		else if (strcmp(key, "api_key")      == 0)
			strncpy(cfg->api_key,      val, sizeof(cfg->api_key)      - 1);
		else if (strcmp(key, "username")     == 0)
			strncpy(cfg->username,     val, sizeof(cfg->username)     - 1);
		else if (strcmp(key, "password")     == 0)
			strncpy(cfg->password,     val, sizeof(cfg->password)     - 1);
		else if (strcmp(key, "download_dir") == 0)
			strncpy(cfg->download_dir, val, sizeof(cfg->download_dir) - 1);
		else if (strcmp(key, "update_host")  == 0)
			strncpy(cfg->update_host,  val, sizeof(cfg->update_host)  - 1);
		else if (strcmp(key, "update_port")  == 0)
			cfg->update_port = atoi(val);
		else if (strcmp(key, "update_check_path") == 0)
			strncpy(cfg->update_check_path, val,
			        sizeof(cfg->update_check_path) - 1);
		else if (strcmp(key, "update_install_path") == 0)
			strncpy(cfg->update_install_path, val,
			        sizeof(cfg->update_install_path) - 1);
	}
	fclose(fp);
	return cfg->server[0] != '\0';
}


/* ==========================================================================
 * Utility: base64 encode (for HTTP Basic auth)
 * ========================================================================== */

static const char b64_chars[] =
	"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

static void base64_encode(const char *in, int len, char *out, int max_out) {
	int i, j = 0;
	for (i = 0; i < len && j < max_out - 4; i += 3) {
		unsigned char a = (unsigned char)in[i];
		unsigned char b = (i+1 < len) ? (unsigned char)in[i+1] : 0;
		unsigned char c = (i+2 < len) ? (unsigned char)in[i+2] : 0;
		out[j++] = b64_chars[a >> 2];
		out[j++] = b64_chars[((a & 3) << 4) | (b >> 4)];
		out[j++] = (i+1 < len) ? b64_chars[((b & 0xF) << 2) | (c >> 6)] : '=';
		out[j++] = (i+2 < len) ? b64_chars[c & 0x3F] : '=';
	}
	if (j < max_out) out[j] = '\0';
}


/* ==========================================================================
 * Utility: URL percent-encoding
 * ========================================================================== */

static void url_encode(const char *src, char *dst, int max) {
	int di = 0;
	for (int si = 0; src[si] && di < max - 4; si++) {
		unsigned char c = (unsigned char)src[si];
		if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
		    (c >= '0' && c <= '9') ||
		    c == '-' || c == '_' || c == '.' || c == '~') {
			dst[di++] = (char)c;
		} else {
			di += snprintf(dst + di, max - di, "%%%02X",
			               (unsigned int)c);
		}
	}
	dst[di] = '\0';
}


/* ==========================================================================
 * Minimal JSON field extractor
 * No heap allocations; operates on a flat char buffer.
 * ========================================================================== */

/*
 * Starting at s[0] == '{', return the index of the matching '}'.
 * Returns -1 if not found.  Handles nested objects/arrays and strings.
 */
static int json_obj_end(const char *s, int len) {
	int i = 1, depth = 1, in_str = 0;
	while (i < len && depth > 0) {
		char c = s[i];
		if (!in_str) {
			if      (c == '"')             in_str = 1;
			else if (c == '{' || c == '[') depth++;
			else if (c == '}' || c == ']') {
				if (--depth == 0) return i;
			}
		} else {
			if      (c == '\\') i++;   /* skip escaped character */
			else if (c == '"')  in_str = 0;
		}
		i++;
	}
	return -1;
}

/*
 * Return a pointer to the value that follows "key": in [s, s+len).
 * Returns NULL if the key is not found.
 */
static const char *json_find_key(const char *s, int len, const char *key) {
	char needle[80];
	int nlen = snprintf(needle, sizeof(needle), "\"%s\":", key);
	for (int i = 0; i <= len - nlen; i++) {
		if (memcmp(s + i, needle, nlen) == 0)
			return s + i + nlen;
	}
	return NULL;
}

/* Extract an integer value; returns 1 on success. */
static int json_int(const char *s, int len, const char *key, int *out) {
	const char *v = json_find_key(s, len, key);
	if (!v) return 0;
	while (*v == ' ' || *v == '\t') v++;
	char *end;
	long val = strtol(v, &end, 10);
	if (end == v) return 0;
	*out = (int)val;
	return 1;
}

/* Extract a string value; returns 1 on success. */
static int json_str(const char *s, int len, const char *key,
                    char *out, int max) {
	const char *v = json_find_key(s, len, key);
	if (!v) return 0;
	while (*v == ' ' || *v == '\t') v++;
	if (*v != '"') return 0;
	v++;
	int i = 0;
	while (*v && i < max - 1) {
		if (*v == '\\') {
			v++;
			switch (*v) {
				case 'n':  out[i++] = '\n'; break;
				case 't':  out[i++] = '\t'; break;
				case '"':  out[i++] = '"';  break;
				case '\\': out[i++] = '\\'; break;
				default:   out[i++] = *v;   break;
			}
			if (*v) v++;
		} else if (*v == '"') {
			break;
		} else {
			out[i++] = *v++;
		}
	}
	out[i] = '\0';
	return 1;
}

/*
 * Case-insensitive substring search (replaces strstr for header parsing).
 */
static const char *stristr(const char *hay, const char *needle) {
	int nlen = strlen(needle);
	while (*hay) {
		int ok = 1;
		for (int i = 0; i < nlen; i++) {
			if (tolower((unsigned char)hay[i]) !=
			    tolower((unsigned char)needle[i])) {
				ok = 0;
				break;
			}
		}
		if (ok) return hay;
		hay++;
	}
	return NULL;
}


/* ==========================================================================
 * HTTP/1.0 client  (dswifi9 BSD socket API)
 * Static buffers keep everything off the DS stack.
 * ========================================================================== */

/* JSON response buffer – reused by every API call (single-threaded DS). */
static char http_buf[ROMM_HTTP_BUF_SIZE];

/* Download chunk buffer – used only during file streaming. */
static char dl_buf[32768];

/* Stream reader recv buffer (4 KB) – used only during cache-build streaming. */
static char sr_buf[4096];

/* zlib inflate output buffer (32 KB) – used during ZIP extraction only. */
static uint8_t inflate_out[32768];

/* Per-item collect buffer – first ~3 KB of each JSON item object.
 * id, name, fs_name appear within the first ~600 bytes of every item,
 * well before the large metadata/files arrays. */
static char item_buf[3072];

/* ---- auth helpers -------------------------------------------------------- */

/*
 * Append authentication query-string parameter if api_key is configured.
 * Writes the final path (with optional ?api_key=…) into buf and returns it.
 */
static void build_url_path(const RommConfig *cfg, const char *path,
                            char *buf, int max) {
	(void)cfg;
	strncpy(buf, path, max - 1);
	buf[max-1] = '\0';
}

/*
 * Build an Authorization header line (Basic auth) when api_key is absent
 * but username is present.  buf receives the full "Authorization: …\r\n"
 * string (empty if not applicable).
 */
static void build_auth_header(const RommConfig *cfg, char *buf, int max) {
	buf[0] = '\0';
	if (cfg->api_key[0]) {
		/* Prefer long-lived client API token as Bearer */
		snprintf(buf, max, "Authorization: Bearer %s\r\n", cfg->api_key);
		return;
	}
	if (!cfg->username[0]) return;

	char creds[128];
	char b64[200];
	snprintf(creds, sizeof(creds), "%s:%s",
	         cfg->username, cfg->password);
	base64_encode(creds, strlen(creds), b64, sizeof(b64));
	snprintf(buf, max, "Authorization: Basic %s\r\n", b64);
}

/* ---- connect ------------------------------------------------------------- */

static int http_connect(const RommConfig *cfg) {
	struct hostent *he = gethostbyname(cfg->server);
	if (!he) {
		romm_log("DNS failed for: %s", cfg->server);
		return -1;
	}
	int sock = socket(AF_INET, SOCK_STREAM, 0);
	if (sock < 0) {
		romm_log("socket() failed");
		return -1;
	}
	struct sockaddr_in addr;
	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	addr.sin_port   = htons((uint16_t)cfg->port);
	addr.sin_addr   = *(struct in_addr *)he->h_addr_list[0];

	if (connect(sock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
		romm_log("connect() failed: %s:%d", cfg->server, cfg->port);
		closesocket(sock);
		return -1;
	}
	return sock;
}

/* ---- header parsing ------------------------------------------------------ */

/*
 * Read HTTP response headers into hdr_buf (one byte at a time to avoid
 * consuming any body bytes).  Returns header length on success, -1 on error.
 */
static int http_read_headers(int sock, char *hdr_buf, int max) {
	int len = 0;
	while (len < max - 1) {
		char c;
		if (recv(sock, &c, 1, 0) <= 0) break;
		hdr_buf[len++] = c;
		if (len >= 4 &&
		    hdr_buf[len-4] == '\r' && hdr_buf[len-3] == '\n' &&
		    hdr_buf[len-2] == '\r' && hdr_buf[len-1] == '\n') {
			hdr_buf[len] = '\0';
			return len;
		}
	}
	hdr_buf[len] = '\0';
	return -1;
}

static int http_parse_status(const char *hdr) {
	const char *sp = strchr(hdr, ' ');
	return sp ? atoi(sp + 1) : -1;
}

static int http_parse_content_length(const char *hdr) {
	const char *p = stristr(hdr, "content-length:");
	return p ? atoi(p + 15) : -1;
}

static int http_parse_is_chunked(const char *hdr) {
	const char *te = stristr(hdr, "transfer-encoding:");
	if (!te) return 0;
	return stristr(te, "chunked") != NULL;
}

/*
 * Read one CRLF-terminated line from socket into buf.
 * Returns line length (excluding CRLF) or -1 on connection error.
 */
static int recv_line(int sock, char *buf, int max) {
	int len = 0;
	while (len < max - 1) {
		char c;
		if (recv(sock, &c, 1, 0) <= 0) return -1;
		if (c == '\n') { buf[len] = '\0'; return len; }
		if (c != '\r') buf[len++] = c;
	}
	buf[len] = '\0';
	return len;
}

/* ---- GET → JSON buffer --------------------------------------------------- */

/*
 * Perform an HTTP/1.0 GET and buffer the entire response body in http_buf.
 * Returns body length on success, -1 on any error.
 * The caller must use http_buf immediately before the next call overwrites it.
 */
static int http_get_json(const RommConfig *cfg, const char *path) {
	char full_path[512];
	build_url_path(cfg, path, full_path, sizeof(full_path));

	char auth_hdr[256];
	build_auth_header(cfg, auth_hdr, sizeof(auth_hdr));

	romm_log("GET %s", full_path);

	int sock = http_connect(cfg);
	if (sock < 0) return -1;

	/* Send HTTP/1.0 GET request */
	char req[1024];
	int req_len = snprintf(req, sizeof(req),
		"GET %s HTTP/1.0\r\n"
		"Host: %s:%d\r\n"
		"%s"
		"\r\n",
		full_path, cfg->server, cfg->port, auth_hdr);
	if (send(sock, req, req_len, 0) < 0) {
		romm_log("send() failed");
		closesocket(sock);
		return -1;
	}

	/* Read response headers */
	char hdr[2048];
	if (http_read_headers(sock, hdr, sizeof(hdr)) < 0) {
		romm_log("Incomplete HTTP headers");
		closesocket(sock);
		return -1;
	}

	int status         = http_parse_status(hdr);
	int content_length = http_parse_content_length(hdr);
	romm_log("HTTP %d  Content-Length: %d", status, content_length);

	if (status != 200) {
		closesocket(sock);
		return -1;
	}

	/* Read body into static buffer (handles plain and chunked bodies) */
	int body_len = 0;
	if (http_parse_is_chunked(hdr)) {
		char chunk_line[32];
		while (1) {
			if (recv_line(sock, chunk_line, sizeof(chunk_line)) < 0) break;
			long chunk_sz = strtol(chunk_line, NULL, 16);
			if (chunk_sz <= 0) break;
			if (body_len + (int)chunk_sz > ROMM_HTTP_BUF_SIZE - 1)
				chunk_sz = ROMM_HTTP_BUF_SIZE - 1 - body_len;
			long remaining = chunk_sz;
			while (remaining > 0) {
				int want = (int)(remaining > 4096 ? 4096 : remaining);
				int r = recv(sock, http_buf + body_len, want, 0);
				if (r <= 0) goto json_body_done;
				body_len += r;
				remaining -= r;
			}
			/* consume trailing CRLF after chunk data */
			{ char crlf[2]; recv(sock, crlf, 2, 0); }
		}
	} else {
		int limit = (content_length > 0 && content_length < ROMM_HTTP_BUF_SIZE - 1)
		            ? content_length
		            : ROMM_HTTP_BUF_SIZE - 1;
		while (body_len < limit) {
			int want = limit - body_len;
			if (want > 4096) want = 4096;
			int r = recv(sock, http_buf + body_len, want, 0);
			if (r <= 0) break;
			body_len += r;
		}
	}
json_body_done:
	http_buf[body_len] = '\0';

	closesocket(sock);
	romm_log("Body received: %d bytes", body_len);
	return body_len;
}

/* Forward declarations for functions defined later in this file */
typedef struct { int sock; int is_chunked; long chunk_rem;
                 int eof; int pos; int len; } SR;
static void sr_init(SR *sr, int sock, int is_chunked);
static int  sr_next(SR *sr);
static void draw_progress(int done, int total_bytes);

/* ---- GET → file stream --------------------------------------------------- */

/*
 * Perform an HTTP/1.0 GET and stream the response body directly to a file.
 * Prints progress to the console.
 * Returns bytes written on success, -1 on error.
 */
static int http_download_to_file(const RommConfig *cfg, const char *path,
                                 const char *local_path) {
	char full_path[512];
	build_url_path(cfg, path, full_path, sizeof(full_path));

	char auth_hdr[256];
	build_auth_header(cfg, auth_hdr, sizeof(auth_hdr));

	romm_log("DOWNLOAD %s -> %s", full_path, local_path);

	int sock = http_connect(cfg);
	if (sock < 0) return -1;

	char req[1024];
	int req_len = snprintf(req, sizeof(req),
		"GET %s HTTP/1.0\r\n"
		"Host: %s:%d\r\n"
		"Connection: close\r\n"
		"%s"
		"\r\n",
		full_path, cfg->server, cfg->port, auth_hdr);
	if (send(sock, req, req_len, 0) < 0) {
		romm_log("send() failed");
		closesocket(sock);
		return -1;
	}

	/* Read headers */
	char hdr[2048];
	if (http_read_headers(sock, hdr, sizeof(hdr)) < 0) {
		romm_log("Incomplete HTTP headers");
		closesocket(sock);
		return -1;
	}

	int status         = http_parse_status(hdr);
	int content_length = http_parse_content_length(hdr);
	romm_log("HTTP %d  Content-Length: %d", status, content_length);

	if (status != 200) {
		closesocket(sock);
		return -1;
	}

	FILE *fp = fopen(local_path, "wb");
	if (!fp) {
		romm_log("Cannot create file: %s", local_path);
		closesocket(sock);
		return -1;
	}

	/* Stream body to file (handles plain Content-Length and chunked bodies) */
	int total = 0;

	if (http_parse_is_chunked(hdr)) {
		/* HTTP/1.1 chunked transfer encoding – decode chunk envelope */
		char chunk_line[32];
		int  chunked_err = 0;
		while (!chunked_err) {
			if (recv_line(sock, chunk_line, sizeof(chunk_line)) < 0) break;
			long chunk_sz = strtol(chunk_line, NULL, 16);
			if (chunk_sz <= 0) break;
			long remaining = chunk_sz;
			while (remaining > 0) {
				int want = (int)(remaining > (long)sizeof(dl_buf)
				                 ? sizeof(dl_buf) : remaining);
				int r = recv(sock, dl_buf, want, 0);
				if (r <= 0) { chunked_err = 1; break; }
				fwrite(dl_buf, 1, r, fp);
				total += r;
				remaining -= r;
			}
			if (!chunked_err) {
				char crlf[2]; recv(sock, crlf, 2, 0);
				draw_progress(total, -1);
				swiWaitForVBlank();
			}
		}
	} else {
		while (content_length < 0 || total < content_length) {
			int want = sizeof(dl_buf);
			if (content_length > 0) {
				int left = content_length - total;
				if (left < want) want = left;
			}
			int r = recv(sock, dl_buf, want, 0);
			if (r <= 0) break;
			fwrite(dl_buf, 1, r, fp);
			total += r;
			draw_progress(total, content_length);
			swiWaitForVBlank();
		}
	}
	printf("\n");

	fclose(fp);
	closesocket(sock);
	romm_log("Download complete: %d bytes", total);
	return total;
}


/* ==========================================================================
 * Supported-platform filter
 * ========================================================================== */

static const char *const supported_slugs[] = {
	"nds", "gba", "gb", "gbc", "genesis", "megadrive", "snes", NULL
};

static int is_supported(const char *fs_slug) {
	for (int i = 0; supported_slugs[i]; i++) {
		/* Case-insensitive compare */
		const char *a = fs_slug, *b = supported_slugs[i];
		int match = 1;
		while (*a || *b) {
			if (tolower((unsigned char)*a) !=
			    tolower((unsigned char)*b)) { match = 0; break; }
			a++; b++;
		}
		if (match) return 1;
	}
	return 0;
}


/* ==========================================================================
 * Public RoMM API functions
 * ========================================================================== */

int romm_get_platforms(const RommConfig *cfg,
                       RommPlatform *out, int max_count) {
	int body = http_get_json(cfg, "/api/platforms");
	if (body < 0) return -1;

	/* Response is a direct JSON array: [{...}, ...] */
	const char *p = http_buf;
	while (*p && *p != '[') p++;
	if (!*p) { romm_log("No JSON array in platforms response"); return 0; }
	p++;  /* skip '[' */

	int count = 0;
	while (*p && count < max_count) {
		while (*p == ' ' || *p == '\t' || *p == '\n' ||
		       *p == '\r' || *p == ',') p++;
		if (*p != '{') break;

		int obj_end = json_obj_end(p, body - (int)(p - http_buf));
		if (obj_end < 0) break;

		RommPlatform pl;
		memset(&pl, 0, sizeof(pl));
		if (json_int(p, obj_end + 1, "id", &pl.id) &&
		    json_str(p, obj_end + 1, "fs_slug",
		             pl.fs_slug, sizeof(pl.fs_slug)) &&
		    is_supported(pl.fs_slug)) {
			json_str(p, obj_end + 1, "name", pl.name, sizeof(pl.name));
			if (!pl.name[0])
				strncpy(pl.name, pl.fs_slug, sizeof(pl.name) - 1);
			out[count++] = pl;
			romm_log("Platform: [%d] %s (%s)",
			         pl.id, pl.name, pl.fs_slug);
		}
		p += obj_end + 1;
	}
	return count;
}


int romm_get_roms(const RommConfig *cfg, int platform_id,
                  int offset, int limit,
                  RommRom *out, int max_count, int *out_total) {
	char path[256];
	snprintf(path, sizeof(path),
	         "/api/roms?platform_ids=%d&limit=%d&offset=%d"
	         "&with_char_index=false&with_filter_values=false",
	         platform_id, limit, offset);

	int body = http_get_json(cfg, path);
	if (body < 0) return -1;

	/* Response: {"items":[...], "total":N, ...} */
	if (out_total) {
		int total = 0;
		json_int(http_buf, body, "total", &total);
		*out_total = total;
	}

	/* Locate "items": [ */
	const char *arr = NULL;
	const char *v = json_find_key(http_buf, body, "items");
	if (v) {
		while (*v == ' ') v++;
		if (*v == '[') arr = v;
	}
	if (!arr) { romm_log("No items array in ROMs response"); return 0; }
	arr++;  /* skip '[' */

	int count = 0;
	const char *p = arr;
	while (*p && count < max_count) {
		while (*p == ' ' || *p == '\t' || *p == '\n' ||
		       *p == '\r' || *p == ',') p++;
		if (*p != '{') break;

		int obj_end = json_obj_end(p, body - (int)(p - http_buf));
		if (obj_end < 0) break;

		RommRom rom;
		memset(&rom, 0, sizeof(rom));
		if (json_int(p, obj_end + 1, "id", &rom.id) &&
		    json_str(p, obj_end + 1, "fs_name",
		             rom.fs_name, sizeof(rom.fs_name))) {
			json_str(p, obj_end + 1, "name", rom.name, sizeof(rom.name));
			if (!rom.name[0])
				strncpy(rom.name, rom.fs_name, sizeof(rom.name) - 1);
			out[count++] = rom;
			romm_log("ROM: [%d] %s", rom.id, rom.name);
		}
		p += obj_end + 1;
	}
	return count;
}


int romm_download_rom(const RommConfig *cfg, int rom_id,
                      const char *fs_name, const char *dest_dir) {
	/* URL-encode the filename for the API path */
	char enc_name[384];
	url_encode(fs_name, enc_name, sizeof(enc_name));

	char api_path[512];
	snprintf(api_path, sizeof(api_path),
	         "/api/roms/%d/content/%s", rom_id, enc_name);

	/* Build local destination path: dest_dir/fs_name */
	char local_path[256];
	snprintf(local_path, sizeof(local_path), "%s/%s", dest_dir, fs_name);

	/* Ensure destination directory exists (best-effort) */
	mkdir(dest_dir, 0755);

	return http_download_to_file(cfg, api_path, local_path);
}


/* ==========================================================================
 * Progress bar  (32-column NDS console)
 *
 * Single overwrite line: [###############] 73% 149/203MB
 * ========================================================================== */

#define PBAR_W 15   /* bar fill characters; total line ≤ 32 cols */

int get_percentage(int done, int total_bytes) {
	if (total_bytes >= 0x100000) {
		int scaled_done = ceil(done/1024);
		int scaled_total = ceil(total_bytes/1024);
		return ceil(((unsigned long)scaled_done*100) / scaled_total);
	}

	return ceil(((unsigned long)done*100) / total_bytes);
}

static void draw_progress(int done, int total_bytes) {
	char bar[PBAR_W + 1];
	memset(bar, ' ', PBAR_W);
	bar[PBAR_W] = '\0';

	char size[12]; 

	if (total_bytes > 0) {
		int pct  = get_percentage(done, total_bytes);
		int fill = ceil(((unsigned long)pct * PBAR_W)/100);
		for (int i = 0; i < fill; i++) bar[i] = '#';

		/* 0x100000 = 1024*1024*/
		if (total_bytes >= 0x100000)
			snprintf(size, sizeof(size), "%d/%dMB",
			         done >> 20, total_bytes >> 20);
		else
			snprintf(size, sizeof(size), "%d/%dKB",
			         done >> 10, total_bytes >> 10);

		printf("\r[%s]%3d%% %-9s", bar, pct, size);
	} else {
		/* Unknown size — marquee animation */
		static int tick = 0;
		int p = tick++ % PBAR_W;
		for (int i = 0; i < PBAR_W; i++)
			bar[i] = (i >= p && i < p + 3) ? '>' : ' ';

		if (done >= 0x100000)
			snprintf(size, sizeof(size), "%dMB   ", done >> 20);
		else
			snprintf(size, sizeof(size), "%dKB   ", done >> 10);

		printf("\r[%s]  ?? %-9s", bar, size);
	}
}

/* ==========================================================================
 * ZIP / platform helpers
 * ========================================================================== */

static int str_ends_with_zip(const char *name) {
	int n = (int)strlen(name);
	return n > 4 &&
	       tolower((unsigned char)name[n-4]) == '.' &&
	       tolower((unsigned char)name[n-3]) == 'z' &&
	       tolower((unsigned char)name[n-2]) == 'i' &&
	       tolower((unsigned char)name[n-1]) == 'p';
}

/*
 * Map a RoMM platform fs_slug to the TwilightMenu++ folder name.
 * dest_dir (from config) is the root; this returns just the subdirectory.
 */
static void platform_subdir(const char *slug, char *buf, int max) {
	struct { const char *slug; const char *dir; } map[] = {
		{ "nds",       "nds"          },
		{ "gba",       "gba"          },
		{ "gb",        "other/gb"     },
		{ "gbc",       "other/gb"     },   /* TwilightMenu shares one GB dir */
		{ "snes",      "other/snes"   },
		{ "genesis",   "other/md"     },
		{ "megadrive", "other/md"     },
		{ NULL, NULL }
	};
	for (int i = 0; map[i].slug; i++) {
		if (strcasecmp(slug, map[i].slug) == 0) {
			snprintf(buf, max, "%s", map[i].dir);
			return;
		}
	}
	snprintf(buf, max, "other/%s", slug);
}


/* ==========================================================================
 * Streaming ZIP extraction  (single-file ZIPs, deflated or stored)
 *
 * One TCP connection.  Parses the ZIP Local File Header inline, then inflates
 * directly to an SD card file.  Peak RAM: dl_buf(32KB) + inflate_out(32KB)
 * + zlib window(32KB internal) = ~96KB regardless of ROM size.
 *
 * Returns uncompressed bytes written, or -1 on error.
 * On a multi-file ZIP the first entry is extracted and the rest silently
 * drained.
 * ========================================================================== */

#define ZIP_SIG         0x04034B50u
#define ZIP_METHOD_STORED   0
#define ZIP_METHOD_DEFLATE  8

static int http_download_and_extract(const RommConfig *cfg,
                                      const char *api_path,
                                      const char *dest_dir,
                                      const char *expected_fs_name) {
	char full_path[512];
	build_url_path(cfg, api_path, full_path, sizeof(full_path));

	char auth_hdr[256];
	build_auth_header(cfg, auth_hdr, sizeof(auth_hdr));

	romm_log("EXTRACT %s -> %s", full_path, dest_dir);

	int sock = http_connect(cfg);
	if (sock < 0) {
		printf("ERR: connect failed\n");
		return -1;
	}

	char req[1024];
	int req_len = snprintf(req, sizeof(req),
		"GET %s HTTP/1.0\r\n"
		"Host: %s:%d\r\n"
		"Connection: close\r\n"
		"%s"
		"\r\n",
		full_path, cfg->server, cfg->port, auth_hdr);
	if (send(sock, req, req_len, 0) < 0) {
		romm_log("send() failed");
		printf("ERR: send failed\n");
		closesocket(sock); return -1;
	}

	char hdr[2048];
	if (http_read_headers(sock, hdr, sizeof(hdr)) < 0) {
		romm_log("Incomplete headers");
		printf("ERR: no HTTP headers\n");
		closesocket(sock); return -1;
	}
	int status = http_parse_status(hdr);
	romm_log("HTTP %d", status);
	if (status != 200) {
		printf("ERR: HTTP %d\n%.40s\n", status, full_path);
		closesocket(sock); return -1;
	}

	SR sr;
	sr_init(&sr, sock, http_parse_is_chunked(hdr));

	/* ---- Parse ZIP Local File Header (30-byte fixed part) ------------ */
	uint8_t lfh[30];
	for (int i = 0; i < 30; i++) {
		int c = sr_next(&sr);
		if (c < 0) {
			romm_log("ZIP: truncated LFH");
			printf("ERR: ZIP truncated LFH\n");
			closesocket(sock); return -1;
		}
		lfh[i] = (uint8_t)c;
	}

	uint32_t sig = (uint32_t)lfh[0] | ((uint32_t)lfh[1] << 8) |
	               ((uint32_t)lfh[2] << 16) | ((uint32_t)lfh[3] << 24);
	if (sig != ZIP_SIG) {
		romm_log("ZIP: bad signature %08X", sig);
		printf("ERR: bad ZIP sig %08lX\n", (unsigned long)sig);
		closesocket(sock); return -1;
	}

	uint16_t method        = (uint16_t)(lfh[8]  | (lfh[9]  << 8));
	uint32_t compressed_sz = (uint32_t)(lfh[18] | (lfh[19] << 8) |
	                                   (lfh[20] << 16) | (lfh[21] << 24));
	uint32_t uncompressed_sz = (uint32_t)(lfh[22] | (lfh[23] << 8) |
	                                     (lfh[24] << 16) | (lfh[25] << 24));
	uint16_t fname_len     = (uint16_t)(lfh[26] | (lfh[27] << 8));
	uint16_t extra_len     = (uint16_t)(lfh[28] | (lfh[29] << 8));

	romm_log("ZIP method=%d cmp=%lu uncmp=%lu fn=%d",
	         method, (unsigned long)compressed_sz,
	         (unsigned long)uncompressed_sz, fname_len);

	if (method != ZIP_METHOD_STORED && method != ZIP_METHOD_DEFLATE) {
		romm_log("ZIP: unsupported method %d", method);
		printf("ERR: ZIP method %d\n(only STORE/DEFLATE ok)\n", method);
		closesocket(sock); return -1;
	}

	/* ---- Read embedded filename ---------------------------------------- */
	char inner_name[128];
	int  fn_copy = (fname_len < (int)sizeof(inner_name) - 1)
	               ? fname_len : (int)sizeof(inner_name) - 1;
	for (int i = 0; i < fname_len; i++) {
		int c = sr_next(&sr);
		if (c < 0) break;
		if (i < fn_copy) inner_name[i] = (char)c;
	}
	inner_name[fn_copy] = '\0';

	/* Skip extra field */
	for (int i = 0; i < extra_len; i++) sr_next(&sr);

	/* ---- Open output file ---------------------------------------------- */
	mkdir(dest_dir, 0755);
	char out_path[256];
	snprintf(out_path, sizeof(out_path), "%s/%s", dest_dir, inner_name);

	FILE *fp = fopen(out_path, "wb");
	if (!fp) {
		romm_log("Cannot create: %s", out_path);
		printf("ERR: can't create file\n%.28s\n", out_path);
		closesocket(sock); return -1;
	}
	romm_log("Extracting to: %s", out_path);
	printf("-> %s\n", inner_name);

	int written = 0;
	int total_for_progress = (int)uncompressed_sz;   /* 0 if data descriptor */

	if (method == ZIP_METHOD_STORED) {
		/* ---- Stored (no compression) ----------------------------------- */
		uint32_t rem = compressed_sz;
		while (rem > 0) {
			uint32_t want = (rem < sizeof(dl_buf)) ? rem
			                                       : (uint32_t)sizeof(dl_buf);
			int got = 0;
			while ((uint32_t)got < want) {
				int c = sr_next(&sr);
				if (c < 0) goto extract_done;
				dl_buf[got++] = (char)c;
			}
			fwrite(dl_buf, 1, got, fp);
			written += got;
			rem     -= (uint32_t)got;
			draw_progress(written, total_for_progress);
			swiWaitForVBlank();
		}
	} else {
		/* ---- Deflate --------------------------------------------------- */
		z_stream strm;
		memset(&strm, 0, sizeof(strm));
		if (inflateInit2(&strm, -15) != Z_OK) {
			romm_log("inflateInit2 failed");
			printf("ERR: zlib init failed\n");
			fclose(fp); closesocket(sock); return -1;
		}

		uint32_t in_total = 0;
		int zret = Z_OK;

		while (zret != Z_STREAM_END) {
			/* Fill input from stream reader into dl_buf */
			int in_want = (int)sizeof(dl_buf);
			if (compressed_sz > 0) {
				uint32_t left = compressed_sz - in_total;
				if ((uint32_t)in_want > left) in_want = (int)left;
			}
			if (in_want == 0) break;

			int in_got = 0;
			while (in_got < in_want) {
				int c = sr_next(&sr);
				if (c < 0) goto inflate_eof;
				dl_buf[in_got++] = (char)c;
			}
inflate_eof:
			in_total += (uint32_t)in_got;
			strm.next_in  = (Bytef *)dl_buf;
			strm.avail_in = (uInt)in_got;

			do {
				strm.next_out  = inflate_out;
				strm.avail_out = sizeof(inflate_out);
				zret = inflate(&strm, Z_NO_FLUSH);
				if (zret == Z_DATA_ERROR || zret == Z_MEM_ERROR) {
					romm_log("inflate error %d", zret);
					goto inflate_abort;
				}
				int out_got = (int)(sizeof(inflate_out) - strm.avail_out);
				fwrite(inflate_out, 1, out_got, fp);
				written += out_got;
			} while (strm.avail_in > 0 && zret != Z_STREAM_END);

			draw_progress(written, total_for_progress);
			swiWaitForVBlank();

			if (in_got == 0) break;   /* sr EOF */
		}

inflate_abort:
		inflateEnd(&strm);
	}

extract_done:
	printf("\n");
	fclose(fp);
	/* Drain remaining socket bytes for clean TCP close */
	{ char drain[256]; while (recv(sock, drain, sizeof(drain), 0) > 0); }
	closesocket(sock);
	romm_log("Extracted: %d bytes -> %s", written, out_path);

	/* Warn if the inner filename doesn't match what we requested —
	 * this indicates a server-side data mismatch (wrong file in ZIP). */
	if (expected_fs_name && expected_fs_name[0]) {
		/* Compare extensions */
		const char *exp_dot = strrchr(expected_fs_name, '.');
		const char *got_dot = strrchr(inner_name, '.');
		if (exp_dot && got_dot &&
		    strcasecmp(exp_dot, got_dot) != 0) {
			printf("[!] SERVER DATA MISMATCH\n");
			printf("Expected ext: %s\n", exp_dot);
			printf("Got     ext: %s\n", got_dot);
			printf("Wrong file on RoMM server!\n");
			romm_log("MISMATCH: expected ext %s got %s",
			         exp_dot, got_dot);
		}
	}
	return written;
}


/* ==========================================================================
 * Stream reader and streaming JSON parser  (used during cache build)
 *
 * RAM budget: sr_buf (4 KB recv) + item_buf (3 KB per item) = ~7 KB total,
 * regardless of how large the server response is.  Handles arbitrarily large
 * per-item objects (e.g. entries where "files" contains 400 KB of data).
 * ========================================================================== */

static void sr_init(SR *sr, int sock, int is_chunked) {
	sr->sock       = sock;
	sr->is_chunked = is_chunked;
	sr->chunk_rem  = 0;
	sr->eof        = 0;
	sr->pos        = 0;
	sr->len        = 0;
}

static int sr_next(SR *sr) {
	if (sr->eof) return -1;
	if (sr->pos < sr->len) return (unsigned char)sr_buf[sr->pos++];
	/* Refill recv page */
	int r;
	if (sr->is_chunked) {
		if (sr->chunk_rem == 0) {
			char line[32];
			if (recv_line(sr->sock, line, sizeof(line)) < 0)
				{ sr->eof = 1; return -1; }
			sr->chunk_rem = strtol(line, NULL, 16);
			if (sr->chunk_rem <= 0) { sr->eof = 1; return -1; }
		}
		int want = (int)(sr->chunk_rem > (long)sizeof(sr_buf)
		                 ? (long)sizeof(sr_buf) : sr->chunk_rem);
		r = recv(sr->sock, sr_buf, want, 0);
		if (r <= 0) { sr->eof = 1; return -1; }
		sr->chunk_rem -= r;
		if (sr->chunk_rem == 0) { char crlf[2]; recv(sr->sock, crlf, 2, 0); }
	} else {
		r = recv(sr->sock, sr_buf, sizeof(sr_buf), 0);
		if (r <= 0) { sr->eof = 1; return -1; }
	}
	sr->pos = 0; sr->len = r;
	return (unsigned char)sr_buf[sr->pos++];
}

/* Scan stream forward until the literal `pat` is found. */
static int sr_find(SR *sr, const char *pat) {
	int plen = (int)strlen(pat);
	int m = 0, c;
	while ((c = sr_next(sr)) >= 0) {
		if (c == (unsigned char)pat[m]) {
			if (++m == plen) return 1;
		} else {
			m = (c == (unsigned char)pat[0]) ? 1 : 0;
		}
	}
	return 0;
}

/* 3-state machine for JSON depth tracking (correctly handles strings). */
typedef enum { JSN = 0, JSS, JSE } JsonSS;

static void js_feed(JsonSS *st, int c, int *depth) {
	switch (*st) {
	case JSN:
		if      (c == '"')             *st = JSS;
		else if (c == '{' || c == '[') ++*depth;
		else if (c == '}' || c == ']') --*depth;
		break;
	case JSS:
		if      (c == '\\') *st = JSE;
		else if (c == '"')  *st = JSN;
		break;
	case JSE: *st = JSS; break;
	}
}

/*
 * Single HTTP GET → stream-parse the "items" JSON array → write RommRom
 * entries directly to fp.  One TCP connection, no full-body buffering.
 * Works for any response size; never allocates more than sr_buf + item_buf.
 */
static int http_stream_roms_to_cache(const RommConfig *cfg,
                                     int platform_id, FILE *fp) {
	char path[256];
	snprintf(path, sizeof(path),
	         "/api/roms?platform_ids=%d&limit=10000&offset=0"
	         "&with_char_index=false&with_filter_values=false",
	         platform_id);

	char auth_hdr[256];
	build_auth_header(cfg, auth_hdr, sizeof(auth_hdr));
	romm_log("STREAM %s", path);

	int sock = http_connect(cfg);
	if (sock < 0) return -1;

	char req[1024];
	int req_len = snprintf(req, sizeof(req),
		"GET %s HTTP/1.0\r\n"
		"Host: %s:%d\r\n"
		"Connection: close\r\n"
		"%s"
		"\r\n",
		path, cfg->server, cfg->port, auth_hdr);
	if (send(sock, req, req_len, 0) < 0) {
		romm_log("send() failed"); closesocket(sock); return -1;
	}

	char hdr[2048];
	if (http_read_headers(sock, hdr, sizeof(hdr)) < 0) {
		romm_log("Incomplete headers"); closesocket(sock); return -1;
	}

	int status = http_parse_status(hdr);
	romm_log("HTTP %d", status);
	if (status != 200) { closesocket(sock); return -1; }

	SR sr;
	sr_init(&sr, sock, http_parse_is_chunked(hdr));

	if (!sr_find(&sr, "\"items\":[")) {
		romm_log("items array not found"); closesocket(sock); return 0;
	}

	int count = 0;
	int c;

	while (!sr.eof) {
		/* Skip whitespace / commas between items */
		do { c = sr_next(&sr); }
		while (c >= 0 && (c==' '||c=='\t'||c=='\n'||c=='\r'||c==','));

		if (c < 0 || c == ']') break;   /* end of array or EOF */
		if (c != '{') continue;          /* unexpected char, skip */

		/* Collect the first sizeof(item_buf)-1 bytes of this object.
		 * After the buffer fills we keep depth-tracking but stop storing. */
		item_buf[0] = '{';
		int ib_len    = 1;
		int collecting = 1;
		int depth     = 1;
		JsonSS ss     = JSN;

		while (depth > 0) {
			c = sr_next(&sr);
			if (c < 0) goto stream_done;
			js_feed(&ss, c, &depth);
			if (collecting) {
				if (ib_len < (int)sizeof(item_buf) - 1)
					item_buf[ib_len++] = (char)c;
				else
					collecting = 0;  /* drain the rest silently */
			}
		}
		if (ib_len >= (int)sizeof(item_buf)) ib_len = (int)sizeof(item_buf) - 1;
		item_buf[ib_len] = '\0';

		/* Extract id + fs_name (required) and name (optional) */
		RommRom rom;
		memset(&rom, 0, sizeof(rom));
		if (json_int(item_buf, ib_len, "id", &rom.id) &&
		    json_str(item_buf, ib_len, "fs_name",
		             rom.fs_name, sizeof(rom.fs_name))) {
			json_str(item_buf, ib_len, "name", rom.name, sizeof(rom.name));
			if (!rom.name[0])
				strncpy(rom.name, rom.fs_name, sizeof(rom.name) - 1);
			fwrite(&rom, sizeof(RommRom), 1, fp);
			count++;
			romm_log("ROM: [%d] %s", rom.id, rom.name);
			if (count % 25 == 0)
				printf("\r%d ROMs cached...   ", count);
		}
	}

stream_done:
	/* Drain remaining bytes so the server gets a clean TCP close. */
	{ char drain[256]; while (recv(sock, drain, sizeof(drain), 0) > 0); }
	closesocket(sock);
	printf("\r%d ROMs cached.     \n", count);
	romm_log("Stream done: %d entries", count);
	return count;
}

/* ==========================================================================
 * Local ROM metadata cache  (SD card binary file)
 *
 * Binary layout (all values native-endian, same as the DS):
 *   [0..3]  uint32  magic      = ROMM_CACHE_MAGIC
 *   [4]     uint8   version    = ROMM_CACHE_VERSION
 *   [5..8]  uint32  platform_id
 *   [9..12] uint32  rom_count
 *   [13..]  RommRom entries    (sizeof(RommRom) each)
 *
 * This keeps all per-platform ROM metadata on the SD card so we never
 * need to hold more than one display page (10 × 196 = ~1.9 KB) in RAM.
 * ========================================================================== */

#define ROMM_CACHE_HDR_SIZE  13   /* 4 + 1 + 4 + 4 */

static void romm_cache_path(int platform_id, char *buf, int max) {
	snprintf(buf, max, "/romm_cache_%d.bin", platform_id);
}

/*
 * Read total ROM count from the cache header.
 * Returns count on success, -1 if the cache is absent or corrupted.
 */
static int romm_cache_get_count(int platform_id) {
	char path[32];
	romm_cache_path(platform_id, path, sizeof(path));
	FILE *fp = fopen(path, "rb");
	if (!fp) return -1;

	uint32_t magic = 0, plat = 0, count = 0;
	uint8_t  ver = 0;
	int ok = (fread(&magic, 4, 1, fp) == 1 && magic == ROMM_CACHE_MAGIC &&
	          fread(&ver,   1, 1, fp) == 1 && ver   == ROMM_CACHE_VERSION &&
	          fread(&plat,  4, 1, fp) == 1 &&
	          fread(&count, 4, 1, fp) == 1);
	fclose(fp);
	return ok ? (int)count : -1;
}

/*
 * Fetch all ROMs for platform_id with a single streaming HTTP GET and
 * write the compact binary cache file to the SD card.
 * Returns total ROMs written, or -1 on error.
 */
static int romm_build_cache(const RommConfig *cfg, int platform_id) {
	char path[32];
	romm_cache_path(platform_id, path, sizeof(path));

	FILE *fp = fopen(path, "wb");
	if (!fp) {
		romm_log("Cannot create cache: %s", path);
		return -1;
	}

	/* Write placeholder header; rom_count patched at the end. */
	uint32_t magic   = ROMM_CACHE_MAGIC;
	uint8_t  ver     = ROMM_CACHE_VERSION;
	uint32_t plat_u  = (uint32_t)platform_id;
	uint32_t count_u = 0;
	fwrite(&magic,   4, 1, fp);
	fwrite(&ver,     1, 1, fp);
	fwrite(&plat_u,  4, 1, fp);
	fwrite(&count_u, 4, 1, fp);

	int total = http_stream_roms_to_cache(cfg, platform_id, fp);
	if (total < 0) {
		fclose(fp);
		remove(path);
		romm_log("Cache build failed");
		return -1;
	}

	/* Patch header: write final rom_count at byte offset 9. */
	fseek(fp, 9, SEEK_SET);
	count_u = (uint32_t)total;
	fwrite(&count_u, 4, 1, fp);
	fclose(fp);

	romm_log("Cache built: %d ROMs -> %s", total, path);
	return total;
}

/*
 * Load `count` ROM entries from the cache file starting at `offset`.
 * Returns the number of entries actually read (may be < count at EOF),
 * or -1 if the cache cannot be opened.
 */
static int romm_cache_load_page(int platform_id, int offset, int count,
                                 RommRom *out) {
	char path[32];
	romm_cache_path(platform_id, path, sizeof(path));
	FILE *fp = fopen(path, "rb");
	if (!fp) return -1;

	long data_pos = (long)ROMM_CACHE_HDR_SIZE + (long)offset * sizeof(RommRom);
	if (fseek(fp, data_pos, SEEK_SET) != 0) {
		fclose(fp);
		return -1;
	}

	int n = 0;
	for (; n < count; n++) {
		if (fread(&out[n], sizeof(RommRom), 1, fp) != 1) break;
	}
	fclose(fp);
	return n;
}


/* ==========================================================================
 * Interactive console UI
 * ========================================================================== */

static void wait_any_key(void) {
	printf("\nPress any key...\n");
	while (1) {
		swiWaitForVBlank();
		scanKeys();
		if (keysDown()) break;
	}
}

/*
 * Generic scrollable list menu.
 * items[]  – array of strings to display
 * count    – number of items
 * title    – header line (max 32 chars)
 * Returns selected index (0-based), or -1 if B / START pressed.
 */
static int menu_select(const char **items, int count, const char *title) {
	int sel   = 0;
	int dirty = 1;

	while (1) {
		swiWaitForVBlank();
		scanKeys();
		int keys = keysDown();

		if (keys & KEY_UP)    { if (--sel < 0) sel = count - 1; dirty = 1; }
		if (keys & KEY_DOWN)  { if (++sel >= count) sel = 0;    dirty = 1; }
		if (keys & KEY_A)     return sel;
		if ((keys & KEY_B) || (keys & KEY_START)) return -1;

		if (!dirty) continue;

		consoleClear();
		printf("%-32.32s\n", title);
		printf("--------------------------------\n");

		/* Show a scrolling window of up to 18 entries */
		int start = sel - 9;
		if (start < 0) start = 0;
		if (start > count - 18) start = count - 18;
		if (start < 0) start = 0;
		int end = start + 18;
		if (end > count) end = count;

		for (int i = start; i < end; i++) {
			if (i == sel)
				printf("> %-28.28s\n", items[i]);
			else
				printf("  %-28.28s\n", items[i]);
		}

		printf("--------------------------------\n");
		printf("UP/DN:nav  A:ok  B:back\n");
		dirty = 0;
	}
}


/* ==========================================================================
 * Self-updater
 *
 * Checks a plain-HTTP version manifest and downloads a new .nds binary to
 * the SD card.  The DS has no TLS stack, so the update server must be
 * reachable over HTTP.  The simplest setup is a one-liner in the nginx
 * config that already serves your RoMM instance:
 *
 *   location /dsload/ {
 *       root /path/to/your/static/files;
 *   }
 *
 * Then drop version.json + dsloadbump.nds in that directory whenever
 * you cut a new GitHub release.  version.json format:
 *   {"version":"2.01","path":"/dsload/dsloadbump.nds","notes":"..."}
 *
 * Defaults (all overridable in /romm.cfg):
 *   update_host         = same as server=
 *   update_port         = same as port=
 *   update_check_path   = /dsload/version.json
 *   update_install_path = /dsloadbump.nds
 * ========================================================================== */

/* Parse "X.YY" or "X.Y" version string to a comparable integer. */
static int version_int(const char *v) {
	int major = atoi(v);
	const char *dot = strchr(v, '.');
	int minor = dot ? atoi(dot + 1) : 0;
	return major * 1000 + minor;
}

int romm_check_update(const RommConfig *cfg) {
	consoleClear();
	printf("=== Check for Updates ===\n\n");
	printf("Current version: v%s\n", ROMM_VERSION);
	printf("github.com/VXisto/dsloadbump\n\n");
	printf("Checking update server...\n");

	/* Build an isolated config: update host + no auth credentials. */
	RommConfig uc;
	memset(&uc, 0, sizeof(uc));
	const char *host = cfg->update_host[0] ? cfg->update_host : cfg->server;
	int  port        = cfg->update_port    ? cfg->update_port  : cfg->port;
	strncpy(uc.server, host, sizeof(uc.server) - 1);
	uc.port = port;
	/* Deliberately no api_key/username/password — update server is public. */

	const char *check_path = cfg->update_check_path[0]
	                         ? cfg->update_check_path
	                         : "/dsload/version.json";

	int body = http_get_json(&uc, check_path);
	if (body < 0) {
		printf("\nCannot reach update server.\n");
		printf("%s:%d%s\n", host, port, check_path);
		printf("\nTo self-host updates, add to\n");
		printf("/romm.cfg:\n");
		printf("  update_host=<your server>\n");
		printf("  update_check_path=/dsload/version.json\n");
		wait_any_key();
		return 0;
	}

	char remote_ver[16]   = {0};
	char remote_path[128] = {0};
	char remote_notes[96] = {0};
	json_str(http_buf, body, "version", remote_ver,   sizeof(remote_ver));
	json_str(http_buf, body, "path",    remote_path,  sizeof(remote_path));
	json_str(http_buf, body, "notes",   remote_notes, sizeof(remote_notes));

	romm_log("Update check: local=v%s remote=v%s", ROMM_VERSION, remote_ver);

	if (!remote_ver[0] || !remote_path[0]) {
		printf("Malformed version manifest.\n");
		printf("Expected JSON with 'version'\n");
		printf("and 'path' keys.\n");
		wait_any_key();
		return 0;
	}

	if (version_int(remote_ver) <= version_int(ROMM_VERSION)) {
		printf("\nYou are up to date!  v%s\n", ROMM_VERSION);
		wait_any_key();
		return 0;
	}

	/* ---- Newer version available ---------------------------------------- */
	consoleClear();
	printf("=== Update Available! ===\n");
	printf("--------------------------------\n");
	printf("Current : v%s\n", ROMM_VERSION);
	printf("New     : v%s\n", remote_ver);
	printf("--------------------------------\n");
	if (remote_notes[0])
		printf("%.32s\n", remote_notes);
	printf("\n");
	printf("A: Download & Install\n");
	printf("B: Later\n");

	int choice = 0;
	while (!choice) {
		swiWaitForVBlank();
		scanKeys();
		int k = keysDown();
		if (k & KEY_B)     { choice = -1; }
		if (k & KEY_A)     { choice  =  1; }
		if (k & KEY_START) { choice = -1; }
	}
	if (choice < 0) return 0;

	/* ---- Download -------------------------------------------------------- */
	const char *install_path = cfg->update_install_path[0]
	                           ? cfg->update_install_path
	                           : "/dsloadbump.nds";

	char tmp_path[132];
	snprintf(tmp_path, sizeof(tmp_path), "%s.tmp", install_path);

	consoleClear();
	printf("Downloading v%s...\n\n", remote_ver);

	int bytes = http_download_to_file(&uc, remote_path, tmp_path);
	if (bytes <= 0) {
		printf("\nERROR: download failed.\n");
		remove(tmp_path);
		romm_log("Update download FAIL: %s%s", host, remote_path);
		wait_any_key();
		return 0;
	}

	/* ---- Install: rename tmp → final ------------------------------------ */
	remove(install_path);
	if (rename(tmp_path, install_path) != 0) {
		printf("\nERROR: could not rename.\n");
		printf("Saved to:\n%.30s\n", tmp_path);
		printf("Rename manually to:\n%.30s\n", install_path);
	} else {
		printf("\n================================\n");
		printf("Updated to v%s!\n", remote_ver);
		printf("%.2f MB installed.\n", (float)bytes / (1024.0f * 1024.0f));
		printf("================================\n");
		printf("\nPlease power off and reboot\nto run the new version.\n");
		romm_log("Update installed: v%s (%d bytes)", remote_ver, bytes);
		wait_any_key();
		return 1;
	}

	wait_any_key();
	return 0;
}


/* ==========================================================================
 * Quick server ROM count – one HTTP GET with limit=1
 * Returns the server's current total for this platform, or -1 on error.
 * ========================================================================== */
static int romm_get_server_count(const RommConfig *cfg, int platform_id) {
	char path[256];
	snprintf(path, sizeof(path),
	         "/api/roms?platform_ids=%d&limit=1&offset=0"
	         "&with_char_index=false&with_filter_values=false",
	         platform_id);
	int body = http_get_json(cfg, path);
	if (body < 0) return -1;
	int total = 0;
	if (!json_int(http_buf, body, "total", &total)) return -1;
	return total;
}


void romm_run_mode(const RommConfig *cfg) {
	romm_log_init();
	romm_log("romm_run_mode: server=%s:%d", cfg->server, cfg->port);

	consoleClear();
	printf("=== RoMM Download Mode ===\n");
	printf("Server: %s:%d\n\n", cfg->server, cfg->port);
	printf("Loading platforms...\n");

	/* --- Fetch supported platforms ---------------------------------------- */
	RommPlatform platforms[ROMM_MAX_PLATFORMS];
	int plat_count = romm_get_platforms(cfg, platforms, ROMM_MAX_PLATFORMS);

	if (plat_count <= 0) {
		printf("\nNo supported platforms found.\n");
		printf("Check server/romm.cfg.\n");
		printf("Log: %s\n", ROMM_LOG_FILE);
		romm_log("No platforms returned (count=%d)", plat_count);
		wait_any_key();
		romm_log_close();
		return;
	}

	/* --- Build platform menu labels --------------------------------------- */
	const char *plat_items[ROMM_MAX_PLATFORMS];
	char plat_labels[ROMM_MAX_PLATFORMS][50];
	for (int i = 0; i < plat_count; i++) {
		snprintf(plat_labels[i], sizeof(plat_labels[i]),
		         "%-28.28s", platforms[i].name);
		plat_items[i] = plat_labels[i];
	}

	/* --- Platform selection loop ------------------------------------------ */
	while (1) {
		int psel = menu_select(plat_items, plat_count, "Select Platform");
		if (psel < 0) break;   /* B pressed – exit RoMM mode */

		int platform_id = platforms[psel].id;

		/* --- Ensure local metadata cache is present and up-to-date ------- */
		consoleClear();
		printf("Checking server...\n");
		int server_total = romm_get_server_count(cfg, platform_id);
		int total        = romm_cache_get_count(platform_id);
		romm_log("Cache check: cached=%d server=%d", total, server_total);

		int needs_rebuild = (total < 0) ||
		                    (server_total > 0 && server_total != total);

		if (needs_rebuild) {
			consoleClear();
			if (total < 0)
				printf("No local cache found.\n");
			else
				printf("Cache outdated:\n local=%d server=%d\nRebuilding...\n\n",
				       total, server_total);
			printf("Fetching ROM list from server...\n\n");
			total = romm_build_cache(cfg, platform_id);
			if (total < 0) {
				printf("\nERROR: Could not build cache.\n");
				printf("Check server/romm.cfg.\nLog: %s\n", ROMM_LOG_FILE);
				wait_any_key();
				continue;   /* back to platform select */
			}
			consoleClear();
			printf("Cache ready: %d ROMs.\n", total);
			swiWaitForVBlank();
			swiWaitForVBlank();
		}

		int offset = 0;

		/* --- ROM browse loop ---------------------------------------------- */
		while (1) {
			RommRom roms[ROMM_MAX_ROMS];
			int rom_count = romm_cache_load_page(platform_id, offset,
			                                      ROMM_PAGE_SIZE, roms);
			if (rom_count < 0) {
				printf("Error reading cache.\n");
				printf("Log: %s\n", ROMM_LOG_FILE);
				romm_log("romm_cache_load_page error (platform=%d offset=%d)",
				         platform_id, offset);
				wait_any_key();
				break;
			}

			if (rom_count == 0) {
				printf("No ROMs in cache.\n");
				wait_any_key();
				break;
			}

			int page_num = offset / ROMM_PAGE_SIZE + 1;
			int page_max = (total + ROMM_PAGE_SIZE - 1) / ROMM_PAGE_SIZE;
			if (page_max < 1) page_max = 1;

			char page_title[36];
			snprintf(page_title, sizeof(page_title),
			         "%.14s  p%d/%d",
			         platforms[psel].name, page_num, page_max);

			/* ROM list input loop */
			int sel    = 0;
			int dirty  = 1;
			int action = 0;  /* 1=download -1=back 2=next -2=prev 3=refresh */

			while (!action) {
				swiWaitForVBlank();
				scanKeys();
				int keys = keysDown();

				if (keys & KEY_UP)   { if (--sel < 0) sel = rom_count-1; dirty=1; }
				if (keys & KEY_DOWN) { if (++sel >= rom_count) sel=0;    dirty=1; }
				if (keys & KEY_A)    { action = 1; }
				if ((keys & KEY_B) || (keys & KEY_START)) { action = -1; }
				if ((keys & KEY_L) && offset > 0) {
					offset -= ROMM_PAGE_SIZE;
					if (offset < 0) offset = 0;
					action = -2;
				}
				if ((keys & KEY_R) && offset + ROMM_PAGE_SIZE < total) {
					offset += ROMM_PAGE_SIZE;
					action = 2;
				}
				if (keys & KEY_SELECT) { action = 3; }  /* rebuild cache */

				if (action || !dirty) { if (action) break; continue; }

				consoleClear();
				printf("%-32.32s\n", page_title);
				printf("--------------------------------\n");
				for (int i = 0; i < rom_count; i++) {
					if (i == sel)
						printf("> %-28.28s\n", roms[i].name);
					else
						printf("  %-28.28s\n", roms[i].name);
				}
				printf("--------------------------------\n");
				printf("A:dl  B:back  L/R:page  SEL:sync\n");
				dirty = 0;
			}

			if (action == -1) break;               /* back to platform select */
			if (action == 2 || action == -2) continue; /* paging – reload page */

			if (action == 3) {
				/* Rebuild cache from server */
				consoleClear();
				printf("Syncing ROM list from server...\n");
				int new_total = romm_build_cache(cfg, platform_id);
				if (new_total < 0) {
					printf("\nERROR: Sync failed.\n");
					printf("Log: %s\n", ROMM_LOG_FILE);
					wait_any_key();
				} else {
					total = new_total;
					if (offset >= total) offset = 0;
					printf("Synced: %d ROMs.\n", total);
					swiWaitForVBlank();
					swiWaitForVBlank();
				}
				continue;
			}

			/* action == 1 – confirm and (optionally) download */

			/* Compute platform-specific destination directory */
			char subdir[32];
			platform_subdir(platforms[psel].fs_slug,
			                subdir, sizeof(subdir));
			char dest_dir[128];
			snprintf(dest_dir, sizeof(dest_dir), "%s/%s",
			         cfg->download_dir, subdir);

			int is_zip = str_ends_with_zip(roms[sel].fs_name);

			consoleClear();
			if (is_zip) {
				printf("=== ZIP File Detected ===\n\n");
				printf("[!] ROM is packaged as ZIP.\n");
				printf("    No unzipper on DS: it will\n");
				printf("    be extracted for you.\n\n");
			} else {
				printf("=== Confirm Download ===\n\n");
			}
			printf("%.28s\n",    roms[sel].name);
			printf("%.28s\n",    roms[sel].fs_name);
			printf("-> %s\n\n",  dest_dir);

			if (is_zip) {
				printf("A:Extract  X:Save ZIP  B:Cancel\n");
			} else {
				printf("A:Download             B:Cancel\n");
			}

			/* 0=cancel 1=download/extract 2=save-zip */
			int choice = 0;
			while (!choice) {
				swiWaitForVBlank();
				scanKeys();
				int k = keysDown();
				if (k & KEY_B) { choice = -1; }
				if (k & KEY_A) { choice = 1; }
				if (is_zip && (k & KEY_X)) { choice = 2; }
			}
			if (choice < 0) continue;

			consoleClear();
			/* Build the API path */
			char enc_name[384];
			url_encode(roms[sel].fs_name, enc_name, sizeof(enc_name));
			char api_path[512];
			snprintf(api_path, sizeof(api_path),
			         "/api/roms/%d/content/%s",
			         roms[sel].id, enc_name);

			if (choice == 1 && is_zip) {
				printf("Extracting [ID:%d]:\n%.28s\n\n",
				       roms[sel].id, roms[sel].fs_name);
			} else {
				printf("Downloading [ID:%d]:\n%.28s\n\n",
				       roms[sel].id, roms[sel].fs_name);
			}
			romm_log("Request: %s", api_path);

			int bytes;
			if (choice == 1 && is_zip) {
				bytes = http_download_and_extract(cfg, api_path, dest_dir,
				                                  roms[sel].fs_name);
			} else {
				/* Save file (ZIP or native) directly */
				mkdir(dest_dir, 0755);
				char local_path[256];
				snprintf(local_path, sizeof(local_path),
				         "%s/%s", dest_dir, roms[sel].fs_name);
				bytes = http_download_to_file(cfg, api_path, local_path);
			}

			if (bytes < 0) {
				printf("\nERROR: operation failed.\n");
				printf("Check %s\n", ROMM_LOG_FILE);
				romm_log("FAIL: %s", roms[sel].fs_name);
			} else {
				printf("\nDone!  %.2f MB\n",
				       (float)bytes / (1024.0f * 1024.0f));
				romm_log("OK: %s  (%d bytes)",
				         roms[sel].fs_name, bytes);
			}

			wait_any_key();
		}  /* ROM browse loop */
	}  /* Platform selection loop */

	romm_log_close();
}
