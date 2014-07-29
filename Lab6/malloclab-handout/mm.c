/*
 * mm.c
 * Name: Fusheng Yuan
 * Andrew ID: fyuan
 * 
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a full description of your solution.
 * description:
 *
 * I choose to use segregated list plus binary search tree to achieve the best
 * performance and space utilization. 
 *
 * Segregated list: I store some small blocks in this list.(Based on
 * my tests, I found 5 small blocks have the most performance and utilization) 
 * This is a two dimensions list, each block that doublesize of 8 
 * in this list is a header for another list that contains same size blocks.  
 * Structure for list: 
 *  [block 8] -> [block 16] -> [block 24] -> [block 32] ....
 *      |             |            |             |
 *  [block 8]    [block 16]    [block 24]    [block 32] ....
 *     .              .            .             .
 *     .              .            .             .
 *
 * Binary search tree: I store all the large block in this tree, and each node
 * in this tree is a header of list that contains same size blocks. For the tree
 * I use the best search strategy to find the suitable block.  
 * Structure for BST:
 *                                 [root 1024]
 *                                /     |     \
 *                               / [block 1024]\
 *                        [left 512]        [right 1536]    
 *                       /     |    \            |     
 *                      / [block 512]\      [block 1536]
 *                     .       .      .          .
 *                      
 * Blocks: I use some strategies to promote the block utilization. 
 * 1. For alloced block, i remove it footer space and use the third
 * byte in its header to store prev block alloc status. 
 * 2. Compress the pointer, even the pointer is 8 bits in 64 machine.
 * I choose to compress the pointer to int before store it, because 
 * we only need delta for the header of heap.
 * Structure for block:
 * <Segregated list block alloced>
 *  [Header: size, pre alloc status, 0, 1]
 *  [point to next same size block]
 *  [point to prev same size block]
 *  [Payload...]
 *
 * <Segregated list block not alloc>
 *  [Header: size, pre alloc status, 0, 0]
 *  [point to next same size block]
 *  [point to prev same size block]
 *  [Payload...]
 *  [footer: size]
 * 
 * <BST block alloced>
 *  [Header: size, pre alloc status, 0, 1]
 *  [point to next same size block]
 *  [point to prev same size block]
 *  [point to the pointer that father point to itself]
 *  [point to the left node]
 *  [point to the right node]
 *  [Payload...]
 *
 * <BST block not alloc>
 *  [Header: size, pre alloc status, 0, 0]
 *  [point to next same size block]
 *  [point to prev same size block]
 *  [point to the pointer that father point to itself]
 *  [point to the left node]
 *  [point to the right node]
 *  [Payload...]
 *  [footer: size]
 */


#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/*
 *  DEFINE HELPER
 *  -----------------
 *  
 *  
 */

/*user-defined the global type*/
typedef void *BP;

/* Global var and data structure pointers */
static char *heap_listp = 0;        /* Pointer to first block */
static BP bst_root;                 /* Root of the BST*/
static BP *fix_root;                /* Header of segregated free lists */
static const unsigned int fix_count = 5;  /* Number of segregated free lists */

/* Helper Functions*/
static BP coalesce(BP bp);
static BP extend_heap(size_t words);
static void place(BP bp, size_t asize);
static BP bst_search(BP node, size_t size);


/*checker functions*/
static void print_block(BP bp);
static void check_header(int verbose);
static void check_block(BP bp, int verbose);
static void check_tree(BP node, int verbose);
static void check_lists(int verbose);
static void check_single_list(BP bp, int verbose);


/* Single word (4) or double word (8) alignment */
#define ALIGNMENT   8

/* Basic constants */
#define WSIZE       4           /* Word and header/footer size (bytes) */
#define DSIZE       8           /* Doubleword size (bytes) */
#define CHUNKSIZE   (1 << 6)    /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)         (*(unsigned int *)(p))
#define PUT(p, val)    (GET(p) = (val))

/* Write header info at address p without modifying prev_alloc */
#define WRITE_HEAD(p, val)         (GET(p) = (GET(p) & 0x4) | (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, get prev_alloc */
#define GET_PREV_ALLOC(bp)  (GET(HDRP(bp)) & 0x4)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLC(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLC(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* given a header, and get next block in the same size list */
#define POINT_TO_NEXT(bp)    (*(unsigned int *)(bp))
#define POINT_TO_PREV(bp)    (*(unsigned int *)((char *)(bp) + WSIZE))

#define FIX_SIZE DSIZE * fix_count

/* compress the space for saving */
static inline unsigned int compress(BP p)
{
    return ((unsigned long)(p) - 0x800000000);
}

/* compress the space to pointer */
static inline BP uncompress(unsigned int w)
{
    return ((w) == 0 ? NULL : (BP)((w) + 0x800000000));
}


/* return address of its left child or right child */
#define LEFT_NODE(bp)       ((BP *)((char *)(bp) + DSIZE * 2))
#define RIGH_NODE(bp)       ((BP *)((char *)(bp) + DSIZE * 3))
/*define the double pointer: the pointer points the pointer that father point to child*/
#define PARENT_NODE(bp)     ((BP **)((char *)(bp) + DSIZE))

#define POINT_TO_LEFT(bp)   (*LEFT_NODE(bp))
#define POINT_TO_RIGH(bp)   (*RIGH_NODE(bp))
#define POINT_TO_PARENT(bp) (*PARENT_NODE(bp))

/*return the pointer its fathter point to child*/
#define POINT_TO_CHLD(bp)   (**PARENT_NODE(bp)) 

/*locate the fix block*/
#define LOC(blocksize) ((blocksize/DSIZE)-1)

/* Set use status for next block */ 
#define SET_NEXT_ALLC(bp)       (GET(HDRP(NEXT_BLC(bp))) |= 0x4)

#define UNSET_NEXT_ALLC(bp){                                \
     GET(HDRP(NEXT_BLC(bp))) &= ~0x4;                       \
     FREE_BLC(bp);                                          \
 }

/* Reset the fields of a free block bp */
#define FREE_BLC(bp)                                                     \
{                                                                        \
    POINT_TO_NEXT(bp) = 0;                                               \
    POINT_TO_PREV(bp) = 0;                                               \
    if (GET_SIZE(HDRP(bp)) > FIX_SIZE)                                   \
    {                                                                    \
        POINT_TO_LEFT(bp) = NULL;                                        \
        POINT_TO_RIGH(bp) = NULL;                                        \
        POINT_TO_PARENT(bp) = NULL;                                      \
    }                                                                    \
}

/*connect two blocks*/
#define CONNECTION_BLOCK(new_head, old_head){              \
    POINT_TO_NEXT(new_head) = compress(old_head);          \
    POINT_TO_PREV(old_head) = compress(new_head);          \
}

/*remove a node from tree*/
#define DELETE_NODE(new_node, old_node){                        \
    POINT_TO_PARENT(new_node) = POINT_TO_PARENT(old_node);      \
    POINT_TO_CHLD(old_node) = new_node;                         \
}

/*attach left and right nodes to parent node*/
#define ATTACH_CHLD(left, right, node){                     \
    if (left){                                              \
        POINT_TO_LEFT(node) = left;                         \
        POINT_TO_PARENT(left) = LEFT_NODE(node);            \
    }                                                       \
    if (right){                                             \
        POINT_TO_RIGH(node) = right;                        \
        POINT_TO_PARENT(right) = RIGH_NODE(node);           \
    }                                                       \
}

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */
#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/*
 *  Helper functions
 *  ----------------
 */

// Check if the given pointer is 8-byte aligned
static inline int aligned(const BP p){
    return ((unsigned long)p % ALIGNMENT) == 0;
}

// Return whether the pointer is in the heap.
static int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

/*remove the block from the tree*/
static inline void delete_from_bst(BP bp){

        BP left = POINT_TO_LEFT(bp), right = POINT_TO_RIGH(bp);
        BP node, tmp;
        if (POINT_TO_NEXT(bp)){
            node = uncompress(POINT_TO_NEXT(bp));
            ATTACH_CHLD(left, right, node);
            DELETE_NODE(node, bp);
            return;
        }
        /*4 cases to delete node from BST*/
        if(!right && !left){
            POINT_TO_CHLD(bp) = NULL;
        }else if(right && !left){
            DELETE_NODE(right, bp);
        }else if(!right && left){
            DELETE_NODE(left, bp);
        }else{
            if(POINT_TO_LEFT(right)){
                node = POINT_TO_LEFT(right);
                while(POINT_TO_LEFT(node)) node = POINT_TO_LEFT(node);
                tmp = POINT_TO_RIGH(node);
                if(tmp){
                    DELETE_NODE(tmp, node);
                }else{
                    POINT_TO_CHLD(node) = NULL;
                }
                DELETE_NODE(node, bp);
                ATTACH_CHLD(left, right, node);
            }else{
                POINT_TO_LEFT(right) = left;
                DELETE_NODE(right, bp);
                POINT_TO_PARENT(left) = LEFT_NODE(right);
            }
        }   
}

/*delete the block from list or tree*/
static inline void delete_block(BP bp){

    BP tmp;
    if (GET_SIZE(HDRP(bp)) > FIX_SIZE && POINT_TO_PARENT(bp)){
        delete_from_bst(bp);
    }
    else if (!POINT_TO_PREV(bp)){
        int index = LOC(GET_SIZE(HDRP(bp)));
        fix_root[index] = uncompress(POINT_TO_NEXT(bp));
    }
    tmp = uncompress(POINT_TO_PREV(bp));
    if (tmp){                                                       
        POINT_TO_NEXT(tmp) = POINT_TO_NEXT(bp); 
    }
    tmp = uncompress(POINT_TO_NEXT(bp));
    if (tmp){                                                       
        POINT_TO_PREV(tmp) = POINT_TO_PREV(bp); 
    }
}

/*
 * insert_block - insert a block into BST or list
 *
 */
static inline void insert_block(BP bp, size_t block_size){

    UNSET_NEXT_ALLC(bp);
    if (block_size > FIX_SIZE){
        BP *cur_node_list = &bst_root,parent_node = NULL, tmp;
        while (*cur_node_list != NULL){
            size_t node_size = GET_SIZE(HDRP(*cur_node_list));
            parent_node = *cur_node_list;
            if(block_size == node_size){
                POINT_TO_NEXT(bp) = POINT_TO_NEXT(parent_node);
                tmp = uncompress(POINT_TO_NEXT(parent_node));
                if(tmp != NULL){
                    POINT_TO_PREV(tmp) = compress(bp);
                }
                CONNECTION_BLOCK(parent_node, bp);
                return;
            }
            if (block_size < node_size)
                cur_node_list = LEFT_NODE(parent_node);
            else
                cur_node_list = RIGH_NODE(parent_node);
        }
        POINT_TO_PARENT(bp) = cur_node_list;
        *cur_node_list = bp;
    }else{
        int index = LOC(block_size);
        if (fix_root[index]){
            CONNECTION_BLOCK(bp, fix_root[index]);
        }
        fix_root[index] = bp;
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes
 * asize should be duplicate of double word
 */
static inline BP find_fit(size_t asize){

    BP fit_block;
    size_t index = LOC(asize);

    if (asize <= FIX_SIZE){
        if (fix_root[index]){
            fit_block = fix_root[index];
            fix_root[index] = uncompress(POINT_TO_NEXT(fit_block));
            delete_block(fit_block);
            return fit_block;
        }
    }
    fit_block = bst_search(bst_root, asize);
    if (fit_block)
        delete_block(fit_block);
    
    return fit_block;
}

/* Function definitions */

/*
 * bst_search - search for a block with requested size or larger in BST.
 */
static BP bst_search(BP node, size_t size){

    if (node == NULL)
        return NULL;

    BP left_node, right_node;
    size_t blc_size = GET_SIZE(HDRP(node));

    if (size == blc_size){
        return node;
    }
    else if (size > blc_size){
        right_node = bst_search(*RIGH_NODE(node), size);
        return right_node;
    }
    else{
        left_node = bst_search(*LEFT_NODE(node), size);
        if (left_node)
            return left_node;
        else
            return node;
    }
}

/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((fix_root = mem_sbrk(FIX_SIZE + 4 * WSIZE)) == (void *)-1)
        return -1;
    heap_listp = (char *)(fix_root + fix_count);
    memset(fix_root, 0, FIX_SIZE);
    
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);
    SET_NEXT_ALLC(heap_listp);
    bst_root = NULL;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * malloc
 */
BP malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free(BP ptr)
{
    if(ptr == 0) return;
    //BP tmp;
    if (!in_heap(ptr) || !aligned(ptr))
        return;

    size_t size = GET_SIZE(HDRP(ptr));
    WRITE_HEAD(HDRP(ptr), PACK(size, 0));
    WRITE_HEAD(FTRP(ptr), PACK(size, 0));
    ptr = coalesce(ptr);
    insert_block(ptr, GET_SIZE(HDRP(ptr)));
}

/*
 * realloc - you may want to look at mm-naive.c
 */
BP realloc(BP oldptr, size_t size)
{

    size_t copysize;
    void *newptr;
    /* if size == 0, then just use free and return NULL */
    if (size == 0) {
        free(oldptr);
        return NULL;
    }
    /* if oldptr == NULL, then just use malloc */
    if (oldptr == NULL) return malloc(size);
    /* if oldptr != NULL, call malloc and copy memory */
    newptr = malloc(size);
    if (!newptr) return 0;
    copysize = GET_SIZE(HDRP(oldptr));
    copysize = (copysize) < (size)? (copysize) : (size);
    memcpy(newptr, oldptr, copysize);
    free(oldptr);

    return newptr;
    
}

/*
 * realloc - you may want to look at mm-naive.c
 */
BP calloc(size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    BP newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static BP coalesce(BP bp)
{
    BP prev, next = NEXT_BLC(bp);

    /* Use GET_PREV_ALLOC to judge if prev block is allocated */
    size_t prev_alloc = GET_PREV_ALLOC(bp);
    size_t next_alloc = GET_ALLOC(HDRP(next));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){            /* Case 1 */
        return bp;
    }else if (prev_alloc && !next_alloc){     /* Case 2 */
        delete_block(next);
        size += GET_SIZE(HDRP(next));
        WRITE_HEAD(HDRP(bp), PACK(size, 0));
        WRITE_HEAD(FTRP(bp), PACK(size, 0));
    }else if (!prev_alloc && next_alloc){     /* Case 3 */
        prev = PREV_BLC(bp);
        delete_block(prev);
        size += GET_SIZE(HDRP(prev));
        WRITE_HEAD(FTRP(bp), PACK(size, 0));
        WRITE_HEAD(HDRP(prev), PACK(size, 0));
        bp = prev;
    }else{                                     /* Case 4 */
        prev = PREV_BLC(bp);
        delete_block(next);
        delete_block(prev);
        size += GET_SIZE(HDRP(prev)) + GET_SIZE(FTRP(next));
        WRITE_HEAD(HDRP(prev), PACK(size, 0));
        WRITE_HEAD(FTRP(next), PACK(size, 0));
        bp = prev;
    }
    FREE_BLC(bp);
    return bp;
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static BP extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    WRITE_HEAD(HDRP(bp), PACK(size, 0));           /* Free block header */
    WRITE_HEAD(FTRP(bp), PACK(size, 0));           /* Free block footer */
    WRITE_HEAD(HDRP(NEXT_BLC(bp)), PACK(0, 1));   /* New epilogue header */
    FREE_BLC(bp);
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * place - Place block of asize bytes at start of free block bp
 *       and split if remainder would be at least minimum block size
 */
static void place(BP bp, size_t asize)
{
    size_t blc_size = GET_SIZE(HDRP(bp)), delta = blc_size - asize;

    if (delta >= (2 * DSIZE)){
        WRITE_HEAD(HDRP(bp), PACK(asize, 1));
        WRITE_HEAD(FTRP(bp), PACK(asize, 1));
        SET_NEXT_ALLC(bp);
        bp = NEXT_BLC(bp);
        WRITE_HEAD(HDRP(bp), PACK(delta, 0));
        WRITE_HEAD(FTRP(bp), PACK(delta, 0));
        bp = coalesce(bp);
        insert_block(bp, delta);
    }
    else{
        WRITE_HEAD(HDRP(bp), PACK(blc_size, 1));
        WRITE_HEAD(FTRP(bp), PACK(blc_size, 1));
        SET_NEXT_ALLC(bp);
    }
}

/*
 *  Check Heap Part
 *  ---------------------
 *  
 */

/*
 * print block 
 *
 */
static void print_block(BP bp){
    size_t is_alloc = GET_ALLOC(HDRP(bp));
    if(is_alloc){
        printf("%p: header[size:%d] footer[size:0]\n", bp,
                GET_SIZE(HDRP(bp)));
    }else{
        printf("%p: header[size:%d] footer[size:%d]\n", bp,
                GET_SIZE(HDRP(bp)), GET_SIZE(FTRP(bp)));
    }
}

/*
 * check header
 *
 */
 static void check_header(int verbose){
    if((GET_SIZE(HDRP(heap_listp)) != DSIZE))
        printf("[Bad prologue header, size worry!]");
    if(!GET_ALLOC(HDRP(heap_listp)))
        printf("[Bad prologue header, not alloc!]");
    if(verbose)
        print_block((BP)heap_listp);
 }

/*
 * check single block
 *
 */
 static void check_block(BP bp, int verbose){
    size_t is_alloc = GET_ALLOC(HDRP(bp));

    if(verbose)
        print_block(bp);

    if(!aligned(bp)){
        printf("bad block:%p, not good size!\n", bp);
    }
    if(is_alloc && (GET_SIZE(HDRP(bp)) != DSIZE)){
        printf("alloced, bad block:%p \n", bp);
    }else if (!is_alloc && (GET_SIZE(HDRP(bp))!= DSIZE ||
     GET_SIZE(FTRP(bp))!= DSIZE)){
        printf("not alloc, bad block:%p \n", bp);
    }
 }
/*
 * check BST tree
 *
 */

static void check_tree(BP node, int verbose){
    if (node == NULL)
        return;
    check_single_list(node, verbose);
    check_tree(LEFT_NODE(node), verbose);
    check_tree(RIGH_NODE(node), verbose);
}

/*
* check single list for same size
*
*/
static void check_single_list(BP bp, int verbose){
    if(bp == NULL) return;
    check_block(bp, verbose);
    check_single_list(uncompress(POINT_TO_NEXT(bp)), verbose);
}
/*
 * check segregated lists  
 *
 */
static void check_lists(int verbose){
    BP bp;
    for(bp = heap_listp; bp != NULL; bp = NEXT_BLC(bp)){
        check_single_list(bp, verbose);
    }
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {

    check_header(verbose);
    check_lists(verbose);
    check_tree(bst_root, verbose);
    return 0;
}
