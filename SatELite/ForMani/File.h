#ifndef File_h
#define File_h

#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>

#ifndef _LARGEFILE64_SOURCE
#define lseek64 ::lseek
#define open64  ::open
#endif

#include <stdint.h>
#include <assert.h>
#include <stdio.h>


typedef unsigned char uchar;
typedef const char cchar;

//=================================================================================================
// A buffered file abstraction with only 'putChar()' and 'getChar()'.


#define File_BufSize 1024   // A small buffer seem to work just as fine as a big one (at least under Linux)

enum FileMode { READ, WRITE };


// WARNING! This code is not thoroughly tested. May contain bugs!

class File {
    int         fd;         // Underlying file descriptor.
    FileMode    mode;       // Reading or writing.
    uchar*      buf;        // Read or write buffer.
    int         size;       // Size of buffer (at end of file, less than 'File_BufSize').
    int         pos;        // Current position in buffer
    bool        own_fd;     // Do we own the file descriptor? If so, will close file in destructor.

public:
    #define DEFAULTS fd(-1), mode(READ), buf(NULL), size(-1), pos(0), own_fd(true)
    File(void) : DEFAULTS {}

    File(int fd, FileMode mode, bool own_fd = true) : DEFAULTS  {
        open(fd, mode, own_fd); }

    File(cchar* name, cchar* mode) : DEFAULTS {
        open(name, mode); }
    #undef DEFAULTS

   ~File(void) {
        close(); }

    void open(int fd, FileMode mode, bool own_fd = true);    // Low-level open. If 'own_fd' is FALSE, descriptor will not be closed by destructor.
    void open(cchar* name, cchar* mode);                     // FILE* compatible interface.
    void close(void);

    bool null(void) {               // TRUE if no file is opened.
        return fd == -1; }

    int releaseDescriptor(void) {   // Don't run UNIX function 'close()' on descriptor in 'File's 'close()'.
        if (mode == READ)
            lseek64(fd, pos - size, SEEK_CUR);
        own_fd = false;
        return fd; }

    FileMode getMode(void) {
        return mode; }

    void setMode(FileMode m) {
        if (m == mode) return;
        if (m == READ){
            flush();
            size = read(fd, buf, File_BufSize);
        }else{
            lseek64(fd, pos - size, SEEK_CUR);
            size = -1; }
        mode = m;
        pos = 0; }

    int getCharQ(void) {            // Quick version with minimal overhead -- don't call this in the wrong mode!
      #ifdef PARANOID
        assert(mode == READ);
      #endif
        if (pos < size) return (uchar)buf[pos++];
        if (size < File_BufSize) return EOF;
        size = read(fd, buf, File_BufSize);
        pos  = 0;
        if (size == 0) return EOF;
        return (uchar)buf[pos++]; }

    int putCharQ(int chr) {         // Quick version with minimal overhead -- don't call this in the wrong mode!
      #ifdef PARANOID
        assert(mode == WRITE);
      #endif
        if (pos == File_BufSize)
            write(fd, buf, File_BufSize),
            pos = 0;
        return buf[pos++] = (uchar)chr; }

    int getChar(void) {
        if (mode == WRITE) setMode(READ);
        return getCharQ(); }

    int putChar(int chr) {
        if (mode == READ) setMode(WRITE);
        return putCharQ(chr); }

    bool eof(void) {
        assert(mode == READ);
        if (pos < size) return false;
        if (size < File_BufSize) return true;
        size = read(fd, buf, File_BufSize);
        pos  = 0;
        if (size == 0) return true;
        return false; }

    void flush(void) {
        assert(mode == WRITE);
        write(fd, buf, pos);
        pos = 0; }

    void  seek(int64_t pos, int whence = SEEK_SET);
    int64_t tell(void);
};


//=================================================================================================
// Some nice helper functions:


void         putUInt (File& out, uint64_t val);
inline uint64_t       getUInt (File& in);
inline uint64_t encode64(int64_t  val)           { return (val >= 0) ? (uint64_t)val << 1 : (((uint64_t)(~val) << 1) | 1); }
inline int64_t  decode64(uint64_t val)           { return ((val & 1) == 0) ? (int64_t)(val >> 1) : ~(int64_t)(val >> 1); }
inline void   putInt  (File& out, int64_t val) { putUInt(out, encode64(val)); }
inline uint64_t getInt  (File& in)             { return decode64(getUInt(in)); }


//=================================================================================================
#endif
