/*
 * mm-EFL5.c - modift on the basis of mm-ELF-base.c, implement two malloc
 * strategies: (1) at the head of the free block , (2) at the tail of the free
 * block. However, the score is basically the same as mm-ELF-base.c, since there
 * is no test data similar to the case I consider in report.
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
#define BSIZE 8            /* double word size (bytes) */
#define CHUNKSIZE (1 << 8) /* extend heap size (bytes) */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)                                                      \
  ((size) | (alloc)) /* pack size and alloc bit into a word (why? in report),  \
                        and size include the size of header and footer.        \
                        Thus, block size >= BSIZE. */
#define READ(ptr) (*(unsigned int *)(ptr)) /* read a word at address ptr */
#define WRITE(ptr, val)                                                        \
  ((*(unsigned int *)(ptr)) =                                                  \
       (unsigned int)(val))              /* write a word at address ptr */
#define GET_SIZE(ptr) (READ(ptr) & ~0x7) /* get size of a block */
#define GET_ALLOC(ptr) (READ(ptr) & 0x1)
/* get alloc bit of a block,  0 -> unallocated, 1 -> allocated */

#define HEADER(ptr)                                                            \
  ((char *)(ptr)-WSIZE) /* given block ptr, get header address of a block      \
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
#define GET_PREV_FREE_BLOCK(ptr)                                               \
  ((READ((char *)(ptr))) == 0                                                  \
       ? NULL                                                                  \
       : ((int *)((long)(READ((char *)(ptr))) +                                \
                  (long)(heap_list)))) /* get previous free block ptr */
#define GET_NEXT_FREE_BLOCK(ptr)                                               \
  ((READ((char *)(ptr) + WSIZE)) == 0                                          \
       ? NULL                                                                  \
       : ((int *)((long)(READ((char *)(ptr) + WSIZE)) +                        \
                  (long)(heap_list)))) /* get next free block ptr */
#define SET_PREV_FREE_BLOCK(ptr, val)                                          \
  (val == 0                                                                    \
       ? (WRITE(((char *)(ptr)), (val)))                                       \
       : (WRITE(((char *)(ptr)),                                               \
                (val - (long)(heap_list))))) /* set previous free block ptr */
#define SET_NEXT_FREE_BLOCK(ptr, val)                                          \
  (val == 0                                                                    \
       ? (WRITE(((char *)(ptr) + WSIZE), (val)))                               \
       : (WRITE(((char *)(ptr) + WSIZE),                                       \
                (val - (long)(heap_list))))) /* set next free block ptr */

/* select fit strategy */
#define FIRST_BEST_FIT

#ifdef FIRST_BEST_FIT
#define MAX_SEARCH_FREE_BLOCK 1
#endif

static char *heap_list;
static char *free_list = NULL;

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

static void *extend_heap(size_t heap_size) {
  char *new_ptr;

  if ((long)(new_ptr = mem_sbrk(heap_size)) == -1)
    return NULL;

  // we don't move the new_ptr forward  because we use the
  // place of the old end block as the new block's header,
  // both 12 bytes
  WRITE(HEADER(new_ptr), PACK(heap_size, 0));
  WRITE(FOOTER(new_ptr), PACK(heap_size, 0));
  WRITE(HEADER(NEXT_BLOCK(new_ptr)), PACK(0, 1));

  return merge_block(new_ptr);
}

static void *merge_block(void *ptr) {
  size_t pre_alloc = GET_ALLOC(HEADER(PREV_BLOCK(ptr)));
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
  return ptr;
}

static void *find_fitted_block(size_t block_size) {
  void *ptr;

#ifdef FIRST_BEST_FIT
  char *best_ptr = NULL;
  size_t min_size = 0, free_block_cnt = 0;
  for (ptr = free_list; ptr != NULL;
       ptr = GET_NEXT_FREE_BLOCK(ptr), free_block_cnt++) {
    if (GET_SIZE(HEADER(ptr)) >= block_size) {
      if (min_size == 0 || GET_SIZE(HEADER(ptr)) < min_size) {
        best_ptr = ptr;
        min_size = GET_SIZE(HEADER(ptr));
      }
    }
    if (free_block_cnt > MAX_SEARCH_FREE_BLOCK && best_ptr != NULL)
      break;
  }
  return best_ptr;
#endif

  return NULL;
}

static void set_block(void *ptr, size_t block_size) {
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
    merge_block(ptr);
  } else {
    // assign alloc bit to 1
    WRITE(HEADER(ptr), PACK(current_block_size, 1));
    WRITE(FOOTER(ptr), PACK(current_block_size, 1));
  }
}

static void remove_free_block(void *ptr) {
  if (ptr == NULL || GET_ALLOC(HEADER(ptr)) == 1)
    return;

  void *prev_free_block = GET_PREV_FREE_BLOCK(ptr);
  void *next_free_block = GET_NEXT_FREE_BLOCK(ptr);

  if (prev_free_block == NULL && next_free_block == NULL) {
    free_list = NULL;
  } else if (prev_free_block == NULL) {
    free_list = next_free_block;
    SET_PREV_FREE_BLOCK(next_free_block, 0);
  } else if (next_free_block == NULL) {
    SET_NEXT_FREE_BLOCK(prev_free_block, 0);
  } else {
    SET_NEXT_FREE_BLOCK(prev_free_block, (long)next_free_block);
    SET_PREV_FREE_BLOCK(next_free_block, (long)prev_free_block);
  }
}

static void insert_free_block(void *ptr) {
  if (ptr == NULL || GET_ALLOC(HEADER(ptr)) == 1) {
    return;
  }

  if (free_list == NULL) {
    free_list = ptr;
    SET_PREV_FREE_BLOCK(ptr, 0);
    SET_NEXT_FREE_BLOCK(ptr, 0);
    return;
  }

  SET_PREV_FREE_BLOCK(ptr, 0);
  SET_NEXT_FREE_BLOCK(ptr, (long)free_list);
  SET_PREV_FREE_BLOCK(free_list, (long)ptr);
  free_list = ptr;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  if ((heap_list = mem_sbrk(4 * WSIZE)) == (void *)-1)
    return -1;
  // init heap
  WRITE(heap_list, 0);
  WRITE(heap_list + (1 * WSIZE), PACK(BSIZE, 1));
  WRITE(heap_list + (2 * WSIZE), PACK(BSIZE, 1));
  WRITE(heap_list + (3 * WSIZE), PACK(0, 1));
  heap_list += BSIZE;
  free_list = NULL;

  // extend heap
  if (extend_heap(CHUNKSIZE) == NULL)
    return -1;
  return 0;
}

/*
 * malloc - Allocate a block by strategy in find_fit().
 */
void *malloc(size_t size) {
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
    return ptr;
  }

  // if there is no fitted block, allocate more memory and
  // place the block
  extend_size = MAX(block_size, CHUNKSIZE);
  if ((ptr = extend_heap(extend_size)) == NULL) {
    return NULL;
  }
  set_block(ptr, block_size);
  return ptr;
}

/*
 * free - Just return the block and try to merge with pre
 * or next block.
 */
void free(void *ptr) {
  if (ptr == NULL)
    return;
  size_t size = GET_SIZE(HEADER(ptr));

  WRITE(HEADER(ptr), PACK(size, 0));
  WRITE(FOOTER(ptr), PACK(size, 0));
  merge_block(ptr);
}

/*
 * realloc - Change the size of the block by mallocing a
 * new block, copying its data, and freeing the old block.
 */
void *realloc(void *oldptr, size_t size) {
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
 * 1. The prologue block is BSIZE(8 byte) and allocated(prevent merge).
 * 2. The epilogue block is 0 byte and allocated(prevent merge).
 * 3. The block size is multiple of BSIZE(8 byte).
 * 4. The pointer heap_list is 8 byte after mem_heap_lo().
 */
void mm_checkheap(int verbose) {
  /*Get gcc to be quiet. */
  verbose = verbose;

  char *ptr;

  // check epilogue and prologue blocks
  if (GET_SIZE(HEADER(heap_list)) != BSIZE ||
      GET_ALLOC(HEADER(heap_list)) != 1 ||
      GET_SIZE(FOOTER(heap_list)) != BSIZE || GET_ALLOC(FOOTER(heap_list)) != 1)
    printf("Prologue block error\n");

  ptr = heap_list;
  while (GET_SIZE(HEADER(ptr)) != 0) {
    ptr = NEXT_BLOCK(ptr);
  }
  if (GET_SIZE(HEADER(ptr)) != 0 || GET_ALLOC(HEADER(ptr)) != 1)
    printf("Epilogue block error\n");

  // check the boundary of heap
  if (mem_heap_lo() + BSIZE != heap_list) {
    printf("mem_heap_lo: %p, heap_head: %p\n", mem_heap_lo(), heap_list);
    printf("Heap boundary error\n");
  }
  if (mem_heap_hi() + 1 != (void *)ptr) {
    printf("mem_heap_hi: %p, heap_end: %p\n", mem_heap_hi(), ptr);
    printf("Heap boundary error\n");
  }

  // check the header and footer of each block
  ptr = heap_list;
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
    if ((unsigned long long)ptr % BSIZE != 0)
      printf("Block alignment error\n");

    // check the continuous of heap
    if (ptr + GET_SIZE(HEADER(ptr)) != NEXT_BLOCK(ptr))
      printf("Block continuous error 1\n");
    if (ptr != heap_list) {
      if (FOOTER(PREV_BLOCK(ptr)) != ptr - BSIZE)
        printf("Block continuous error 2\n");
    }

    ptr = NEXT_BLOCK(ptr);
  }

  // check merge
  int cnt = 0;
  ptr = heap_list;
  while (GET_SIZE(HEADER(ptr)) != 0) {
    if (GET_ALLOC(HEADER(ptr)) == 0 && GET_ALLOC(HEADER(NEXT_BLOCK(ptr))) == 0)
      printf("Merge error at block %p\n", ptr);
    ptr = NEXT_BLOCK(ptr);
    cnt++;
  }

  // check the free list
  ptr = free_list;
  while (ptr != NULL) {
    if (!((char *)mem_heap_lo() < ptr && ptr < (char *)mem_heap_hi()))
      printf("Free list boundary error\n");

    if (GET_ALLOC(HEADER(ptr)) != 0)
      printf("Allocated block in the free list at %p\n", ptr);

    if (GET_PREV_FREE_BLOCK(ptr) != NULL &&
        (char *)GET_NEXT_FREE_BLOCK(GET_PREV_FREE_BLOCK(ptr)) != ptr)
      printf("Prev and next pointer error at %p\n", ptr);

    void *tmp = heap_list;
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
