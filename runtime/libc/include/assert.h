// 7.2 Diagnostics<assert.h>

// 7.2.1 assert must be redefined each time
#undef assert

#ifdef NDEBUG
#define assert(ignore)	((void)0)
#endif

#define assert(X)	__builtin_assert(X)

#define static_assert	_Static_assert
