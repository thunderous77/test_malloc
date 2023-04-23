/*
 * mm-SFL.c - modify on the basis of mm-EFL-base.c, change explicit free list to
 * segregated free list. The performance is a little better than mm-EFL.c(score
 * 92).
 */
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#else
#define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4            /* header/footer size (bytes) */
#define DSIZE 8            /* double word size (bytes) */
#define BSIZE 12           /* empty block size (bytes) */
#define CHUNKSIZE (1 << 8) /* extend heap size (bytes) */
#define CLASSNUM 2         /* number of classes -- (0,16], (17, 32] ... */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)                                                      \
  ((size) | (alloc)) /* pack size and alloc bit into a word (why? in report),  \
                        and size include the size of header and footer.        \
                        Thus, block size >= BSIZE. */
#define READ(ptr) (*(unsigned int *)(ptr)) /* read a word at address ptr */
#define WRITE(ptr, val)                                                        \
  ((*(unsigned int *)(ptr)) =                                                  \
       (unsigned int)(val))              /* write a word at address ptr */
#define GET_SIZE(ptr) (READ(ptr) & ~0x3) /* get size of a block */
#define GET_ALLOC(ptr) (READ(ptr) & 0x1)
/* get alloc bit of a block,  0 -> unallocated, 1 -> allocated */

#define HEADER(ptr)                                                            \
  ((char *)(ptr)-DSIZE) /* given block ptr, get header address of a block      \
                         */
#define FOOTER(ptr)                                                            \
  ((char *)(ptr) + GET_SIZE(HEADER(ptr)) -                                     \
   BSIZE) /* given block ptr, get footer address of a block */
#define NEXT_BLOCK(ptr)                                                        \
  ((char *)(ptr) +                                                             \
   GET_SIZE(HEADER(ptr))) /* given block ptr, get next block ptr */
#define PREV_BLOCK(ptr)                                                        \
  ((char *)(ptr)-GET_SIZE(                                                     \
      ((char *)(ptr)-BSIZE))) /* given block ptr, get previous block ptr */
#define GET_NEXT_FREE_BLOCK(ptr)                                               \
  ((READ((char *)(ptr)-WSIZE)) == 0                                            \
       ? NULL                                                                  \
       : ((int *)((long)(READ((char *)(ptr)-WSIZE)) +                          \
                  (long)(heap_list)))) /* get next free block ptr */
#define SET_NEXT_FREE_BLOCK(ptr, val)                                          \
  (val == 0                                                                    \
       ? (WRITE(((char *)(ptr)-WSIZE), (val)))                                 \
       : (WRITE(((char *)(ptr)-WSIZE),                                         \
                (val - (long)(heap_list))))) /* set next free block ptr */
#define GET_CLASS_HEAD(num)                                                    \
  (READ((char *)(heap_list) + (num)*WSIZE)) == 0                               \
      ? NULL                                                                   \
      : ((int *)((long)(READ((char *)(heap_list) + (num)*WSIZE)) +             \
                 (long)(heap_list)))
/* get the head address of the class list */
#define SET_CLASS_HEAD(num, val)                                               \
  (val == 0 ? (WRITE(((char *)(heap_list) + (num)*WSIZE), (val)))              \
            : (WRITE(((char *)(heap_list) + (num)*WSIZE),                      \
                     (val - (long)(heap_list))))) /* set the head address of   \
                                                     the class list */

/* select fit strategy */
#define FIRST_BEST_FIT

#ifdef FIRST_BEST_FIT
#define MAX_SEARCH_FREE_BLOCK 7
#endif

static char *heap_list;

// debug
int cur_func, pre_func;

// extend the heap by creating a new block and a new end
// block return the start address of the new block after
// merge
static void *extend_heap(size_t heap_size);

// merge the block with its previous and next block if
// they are free always input a new free block
static void *merge_block(void *ptr);

// find a free block that fits the size
static void *find_fitted_block(size_t block_size);

// set the block's header and footer
static void set_block(void *ptr, size_t block_size);

// remove the block from the free list
static void remove_free_block(void *ptr);

// insert the block to the free list
static void insert_free_block(void *ptr);

// search the belonged class and return the class number (base 0)
static int search_class(int size);

static void *extend_heap(size_t heap_size) {
  // printf("extend heap begin\n");
  cur_func = 1;
  char *new_ptr;

  if ((long)(new_ptr = mem_sbrk(heap_size)) == -1)
    return NULL;

  // we don't move the new_ptr forward  because we use the
  // place of the old end block as the new block's header,
  // both 8 bytes
  WRITE(HEADER(new_ptr), PACK(heap_size, 0));
  WRITE(FOOTER(new_ptr), PACK(heap_size, 0));
  SET_NEXT_FREE_BLOCK(new_ptr, 0);
  WRITE(HEADER(NEXT_BLOCK(new_ptr)), PACK(0, 1));

  // printf("extend heap end\n");
  return merge_block(new_ptr);
}

static void *merge_block(void *ptr) {
  // printf("merge block begin at %p\n", ptr);
  cur_func = 2;
  // printf("read at %p,size is %d\n", (char *)ptr - BSIZE,
  //  GET_SIZE((char *)ptr - BSIZE));
  // printf("previous block at %p, size %d, alloc %d\n", PREV_BLOCK(ptr),
  //        GET_SIZE(HEADER(PREV_BLOCK(ptr))),
  //        GET_ALLOC(HEADER(PREV_BLOCK(ptr))));
  size_t pre_alloc = GET_ALLOC(HEADER(PREV_BLOCK(ptr)));
  // printf("next block at %p, size %d, alloc %d\n", NEXT_BLOCK(ptr),
  //        GET_SIZE(HEADER(NEXT_BLOCK(ptr))),
  //        GET_ALLOC(HEADER(NEXT_BLOCK(ptr))));
  size_t nxt_alloc = GET_ALLOC(HEADER(NEXT_BLOCK(ptr)));
  size_t block_size = GET_SIZE(HEADER(ptr));

  if (pre_alloc && nxt_alloc) {
    // don't return, still need to insert the block to the
    // free list
  } else if (pre_alloc && !nxt_alloc) {
    remove_free_block(NEXT_BLOCK(ptr));
    block_size += GET_SIZE(HEADER(NEXT_BLOCK(ptr)));
    WRITE(HEADER(ptr), PACK(block_size, 0));
    WRITE(FOOTER(ptr), PACK(block_size, 0));
  } else if (!pre_alloc && nxt_alloc) {
    remove_free_block(PREV_BLOCK(ptr));
    block_size += GET_SIZE(HEADER(PREV_BLOCK(ptr)));
    WRITE(FOOTER(ptr), PACK(block_size, 0));
    WRITE(HEADER(PREV_BLOCK(ptr)), PACK(block_size, 0));
    ptr = PREV_BLOCK(ptr);
  } else {
    remove_free_block(PREV_BLOCK(ptr));
    remove_free_block(NEXT_BLOCK(ptr));
    block_size +=
        GET_SIZE(HEADER(PREV_BLOCK(ptr))) + GET_SIZE(HEADER(NEXT_BLOCK(ptr)));
    WRITE(HEADER(PREV_BLOCK(ptr)), PACK(block_size, 0));
    WRITE(FOOTER(NEXT_BLOCK(ptr)), PACK(block_size, 0));
    ptr = PREV_BLOCK(ptr);
  }
  insert_free_block(ptr);
  // printf("merge block end\n");
  return ptr;
}

static void *find_fitted_block(size_t block_size) {
  // printf("find fitted block begin\n");
  // printf("find fitted block begin, size %d\n", block_size);
  // for (int i = 0; i < CLASSNUM; i++) {
  //   if ((GET_CLASS_HEAD(i)) != NULL) {
  //     int cnt = 0;
  //     int *ptr = GET_CLASS_HEAD(i);
  //     while (ptr != NULL) {
  //       cnt++;
  //       ptr = GET_NEXT_FREE_BLOCK(ptr);
  //     }
  //     printf("class %d, free block cnt %d\n", i, cnt);
  //   }
  // }
  cur_func = 3;
  void *ptr;

#ifdef FIRST_BEST_FIT
  int class_num = search_class(block_size);
  char *best_ptr = NULL;
  size_t min_size = 0, free_block_cnt = 0;
  for (int i = class_num; i < CLASSNUM; i++) {
    if ((ptr = GET_CLASS_HEAD(i)) != NULL) {
      break;
    }
  }
  for (; ptr != NULL; ptr = GET_NEXT_FREE_BLOCK(ptr), free_block_cnt++) {
    if (GET_SIZE(HEADER(ptr)) >= block_size) {
      if (min_size == 0 || GET_SIZE(HEADER(ptr)) < min_size) {
        best_ptr = ptr;
        min_size = GET_SIZE(HEADER(ptr));
      }
    }
    if (free_block_cnt > MAX_SEARCH_FREE_BLOCK && best_ptr != NULL)
      break;
  }
  // printf("find fitted block end\n");
  // printf("find fitted block end, best ptr size %d\n", min_size);
  return best_ptr;
#endif

  return NULL;
}

static void set_block(void *ptr, size_t block_size) {
  // printf("set block at %p begin\n", ptr);
  cur_func = 4;
  size_t current_block_size = GET_SIZE(HEADER(ptr));
  remove_free_block(ptr);

  // if the block size is larger than the required size,
  // split the block
  if (current_block_size - block_size > BSIZE) {
    WRITE(HEADER(ptr), PACK(block_size, 1));
    WRITE(FOOTER(ptr), PACK(block_size, 1));
    ptr = NEXT_BLOCK(ptr);
    WRITE(HEADER(ptr), PACK(current_block_size - block_size, 0));
    WRITE(FOOTER(ptr), PACK(current_block_size - block_size, 0));
    SET_NEXT_FREE_BLOCK(ptr, 0);
    merge_block(ptr);
  } else {
    // assign alloc bit to 1
    WRITE(HEADER(ptr), PACK(current_block_size, 1));
    WRITE(FOOTER(ptr), PACK(current_block_size, 1));
  }
  // printf("set block end\n");
}

static void remove_free_block(void *ptr) {
  // printf("remove free block at %p begin\n", ptr);
  if (ptr == NULL || GET_ALLOC(HEADER(ptr)) == 1)
    return;

  int class_num = search_class(GET_SIZE(HEADER(ptr)));
  char *free_list = (char *)(GET_CLASS_HEAD(class_num));
  // printf("block size %d, class number is %d\n", GET_SIZE(HEADER(ptr)),
  //        search_class(GET_SIZE(HEADER(ptr))));
  // printf("free list at %p\n", free_list);
  if (free_list == ptr) {
    // printf("next free block at %p\n", (char *)GET_NEXT_FREE_BLOCK(ptr));
    free_list = (char *)GET_NEXT_FREE_BLOCK(ptr);
    // printf("set class %d head to %p\n", class_num, free_list);
    SET_CLASS_HEAD(class_num, (long)free_list);
    // printf("remove free block end\n");
    return;
  }

  void *pre_ptr = free_list;
  while (pre_ptr != NULL && GET_NEXT_FREE_BLOCK(pre_ptr) != ptr) {
    // printf("previous free block at %p, next free block at %p", pre_ptr,
    //        (char *)GET_NEXT_FREE_BLOCK(pre_ptr));
    pre_ptr = GET_NEXT_FREE_BLOCK(pre_ptr);
  }
  SET_NEXT_FREE_BLOCK(pre_ptr, (long)GET_NEXT_FREE_BLOCK(ptr));
  SET_NEXT_FREE_BLOCK(ptr, 0);
  // printf("remove free block end\n");
}

static void insert_free_block(void *ptr) {
  // printf("insert free block at %p begin\n", ptr);
  if (ptr == NULL || GET_ALLOC(HEADER(ptr)) == 1) {
    return;
  }

  int class_num = search_class(GET_SIZE(HEADER(ptr)));
  char *free_list = (char *)(GET_CLASS_HEAD(class_num));
  // printf("block size %d, class number is %d\n", GET_SIZE(HEADER(ptr)),
  //  search_class(GET_SIZE(HEADER(ptr))));
  // printf("free list at %p\n", free_list);

  if (free_list == NULL) {
    SET_CLASS_HEAD(class_num, (long)ptr);
    SET_NEXT_FREE_BLOCK(ptr, 0);
    return;
  }

  SET_NEXT_FREE_BLOCK(ptr, (long)free_list);
  SET_CLASS_HEAD(class_num, (long)ptr);
  // printf("insert free block end\n");
}

static int search_class(int size) {
  int i;
  for (i = 4; i < 4 + CLASSNUM; i++) {
    if (size <= (1 << i))
      return i - 4;
  }
  return CLASSNUM - 1;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  // printf("mm_init begin\n");
  if ((heap_list = mem_sbrk((6 + CLASSNUM) * WSIZE)) == (void *)-1)
    return -1;
  // init heap
  for (int i = 0; i < CLASSNUM; i++) {
    WRITE(heap_list + (i * WSIZE), 0);
  }
  WRITE(heap_list + CLASSNUM * WSIZE, PACK(2 * DSIZE, 1));
  WRITE(heap_list + CLASSNUM * WSIZE + (1 * WSIZE), 0);
  WRITE(heap_list + CLASSNUM * WSIZE + (2 * WSIZE), 0);
  WRITE(heap_list + CLASSNUM * WSIZE + (3 * WSIZE), PACK(2 * DSIZE, 1));
  WRITE(heap_list + CLASSNUM * WSIZE + (4 * WSIZE), PACK(0, 1));
  WRITE(heap_list + CLASSNUM * WSIZE + (5 * WSIZE), 0);

  // extend heap
  if (extend_heap(CHUNKSIZE) == NULL)
    return -1;
  // printf("mm_init end\n");
  return 0;
}

/*
 * malloc - Allocate a block by strategy in find_fit().
 */
void *malloc(size_t size) {
  // printf("malloc begin\n");
  // block_size includes header and footer
  size_t block_size;
  size_t extend_size;
  char *ptr;

  if (size == 0) {
    return NULL;
  }

  block_size = ALIGN(size + BSIZE);

  if ((ptr = find_fitted_block(block_size)) != NULL) {
    set_block(ptr, block_size);
    // printf("malloc end\n");
    return ptr;
  }

  // if there is no fitted block, allocate more memory and
  // place the block
  extend_size = MAX(block_size, CHUNKSIZE);
  if ((ptr = extend_heap(extend_size)) == NULL) {
    return NULL;
  }
  set_block(ptr, block_size);
  // printf("malloc end\n");
  return ptr;
}

/*
 * free - Just return the block and try to merge with pre
 * or next block.
 */
void free(void *ptr) {
  // printf("free begin\n");
  if (ptr == NULL)
    return;
  size_t size = GET_SIZE(HEADER(ptr));

  WRITE(HEADER(ptr), PACK(size, 0));
  WRITE(FOOTER(ptr), PACK(size, 0));
  SET_NEXT_FREE_BLOCK(ptr, 0);
  merge_block(ptr);
  // printf("free end\n");
}

/*
 * realloc - Change the size of the block by mallocing a
 * new block, copying its data, and freeing the old block.
 */
void *realloc(void *oldptr, size_t size) {
  // printf("realloc begin\n");
  if (oldptr == NULL) {
    return malloc(size);
  }
  if (size == 0) {
    free(oldptr);
    return NULL;
  }

  void *newptr;
  size_t copySize;
  newptr = malloc(size);
  size = GET_SIZE(HEADER(oldptr));
  copySize = GET_SIZE(HEADER(newptr));
  if (size < copySize)
    copySize = size;
  memcpy(newptr, oldptr, copySize - BSIZE);
  free(oldptr);
  // printf("realloc end\n");
  return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * mm_checkheap - Check the heap.
 * The constant of the heap is as follows.
 * 1. The prologue block is 16 byte and allocated(prevent merge).
 * 2. The epilogue block is 0 byte and allocated(prevent merge).
 * 3. The block size is multiple of BSIZE(8 byte).
 * 4. The pointer heap_list is 16 byte after mem_heap_lo().
 */
void mm_checkheap(int verbose) {
  /*Get gcc to be quiet. */
  // printf("mm_checkheap begin\n");
  verbose = verbose;

  char *ptr, *heap_list_shadow;
  heap_list_shadow = heap_list + CLASSNUM * WSIZE + 2 * WSIZE;

  // check epilogue and prologue blocks
  if (GET_SIZE(HEADER(heap_list_shadow)) != 2 * DSIZE ||
      GET_ALLOC(HEADER(heap_list_shadow)) != 1 ||
      GET_SIZE(FOOTER(heap_list_shadow)) != 2 * DSIZE ||
      GET_ALLOC(FOOTER(heap_list_shadow)) != 1) {
    printf("Prologue block error\n");
    printf("head size: %d, head alloc: %d\n",
           GET_SIZE(HEADER(heap_list_shadow)),
           GET_ALLOC(HEADER(heap_list_shadow)));
    printf("foot size: %d, foot alloc: %d\n",
           GET_SIZE(FOOTER(heap_list_shadow)),
           GET_ALLOC(FOOTER(heap_list_shadow)));
  }

  ptr = heap_list_shadow;
  while (GET_SIZE(HEADER(ptr)) != 0) {
    ptr = NEXT_BLOCK(ptr);
  }
  if (GET_SIZE(HEADER(ptr)) != 0 || GET_ALLOC(HEADER(ptr)) != 1)
    printf("Epilogue block error\n");

  // check the boundary of heap
  if (mem_heap_lo() != heap_list) {
    printf("mem_heap_lo: %p, heap_head: %p\n", mem_heap_lo(), heap_list);
    printf("Heap boundary error\n");
  }
  if (mem_heap_hi() + 1 != (void *)ptr) {
    printf("mem_heap_hi: %p, heap_end: %p\n", mem_heap_hi(), ptr);
    printf("Heap boundary error\n");
  }

  // check the header and footer of each block
  ptr = heap_list_shadow;
  while (GET_SIZE(HEADER(ptr)) != 0) {
    // check the consistency of prev and next pointers
    if (PREV_BLOCK(NEXT_BLOCK(ptr)) != ptr) {
      printf("Prev and next pointers error at %p\n", ptr);
    }

    // check the consistency of header and footer
    if (GET_SIZE(HEADER(ptr)) != GET_SIZE(FOOTER(ptr))) {
      printf("Header and footer size error at %p\n", ptr);
    } else if (GET_ALLOC(HEADER(ptr)) != GET_ALLOC(FOOTER(ptr)))
      printf("Header and footer alloc error\n");

    // address alignment
    if ((unsigned long long)ptr % DSIZE != 0)
      printf("Block alignment error\n");

    // check the continuous of heap
    if (ptr + GET_SIZE(HEADER(ptr)) != NEXT_BLOCK(ptr))
      printf("Block continuous error 1\n");
    if (ptr != heap_list_shadow) {
      if (FOOTER(PREV_BLOCK(ptr)) != ptr - BSIZE)
        printf("Block continuous error 2\n");
    }

    ptr = NEXT_BLOCK(ptr);
  }

  // check merge
  ptr = heap_list_shadow;
  while (GET_SIZE(HEADER(ptr)) != 0) {
    if (GET_SIZE(HEADER(NEXT_BLOCK(ptr))) != 0) {
      if (GET_ALLOC(HEADER(ptr)) == 0 &&
          GET_ALLOC(HEADER(NEXT_BLOCK(ptr))) == 0)
        printf("Merge error at block %p\n", ptr);
    }
    ptr = NEXT_BLOCK(ptr);
  }

  // check the free list
  for (int i = 0; i < CLASSNUM; i++) {
    // printf("class num: %d\n", i);
    ptr = (char *)(GET_CLASS_HEAD(i));
    while (ptr != NULL) {
      // printf("ptr: %p\n", ptr);
      if (!((char *)mem_heap_lo() < ptr && ptr < (char *)mem_heap_hi()))
        printf("Free list boundary error\n");

      if (GET_ALLOC(HEADER(ptr)) != 0)
        printf("Allocated block in the free list at %p\n", ptr);

      void *tmp = heap_list_shadow;
      while (GET_SIZE(HEADER(ptr)) != 0) {
        if (tmp == ptr)
          break;
        tmp = NEXT_BLOCK(tmp);
      }
      if (GET_SIZE(HEADER(tmp)) == 0)
        printf("Block in free list is not in the heap\n");
      ptr = (char *)GET_NEXT_FREE_BLOCK(ptr);
    }
  }

  // printf("mm_checkheap end\n");
}
