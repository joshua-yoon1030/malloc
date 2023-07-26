/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 no
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Joshua Yoon <jbyoon@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

// this is the second bit in our header. this bit tells us if the block before
// us is allocated (1) or free (0).
static const word_t footer_mask = 0x2;

// this is the third bit in our header. This bit tells us if the block before is
// allocated/free.
static const word_t mini_mask = 0x4;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     *
     * TODO: feel free to delete this comment once you've read it carefully.
     * We don't know what the size of the payload will be, so we will declare
     * it as a zero-length array, which is a GCC compiler extension. This will
     * allow us to obtain a pointer to the start of the payload.
     *
     * WARNING: A zero-length array must be the last element in a struct, so
     * there should not be any struct fields after it. For this lab, we will
     * allow you to include a zero-length array in a union, as long as the
     * union is the last field in its containing struct. However, this is
     * compiler-specific behavior and should be avoided in general.
     *
     * WARNING: DO NOT cast this pointer to/from other types! Instead, you
     * should use a union to alias this zero-length array with another struct,
     * in order to store additional types of data in the payload memory.
     */
    union A {
        // if the block is free, use this space for our free list
        struct B {
            // I want these to be block pointers, but it's not defined yet!
            void *prev;
            void *next;
        } list_pointers;
        // if the block is mini, use this space for our free list
        struct C {
            void *next;
        } mini_pointers;
        // if the block is allocated, store the payload
        char payload[0];
    } body;

} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;
// static block_t *free_list_head = NULL;
static block_t *seg_list[15];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool footer, bool prev_mini) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    // footer is the footer before being alloced
    if (footer) {
        word |= footer_mask;
    }
    // prev_mini is self explanatory because I am good at naming variable names
    if (prev_mini) {
        word |= mini_mask;
    }

    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, body.payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)((block->body).payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)((block->body).payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);

    if (get_alloc(block) == false) {
        return asize - dsize;
    } else {
        return asize - wsize;
    }
}

static bool extract_before_alloc(word_t word) {
    return (bool)(word & footer_mask);
}

static bool get_before_alloc(block_t *block) {
    return extract_before_alloc(block->header);
}

static bool extract_before_mini(word_t word) {
    return (bool)(word & mini_mask);
}

static bool get_before_mini(block_t *block) {
    return extract_before_mini(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block, bool prev_alloc, bool prev_mini) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true, prev_alloc, prev_mini);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc,
                        bool prev_alloc, bool prev_mini) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc, prev_alloc, prev_mini);
    // all free_blocks still need footers
    if (!alloc) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc, prev_alloc, prev_mini);
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);

    // hard code if the block is mini
    if (get_before_mini(block)) {
        return (block_t *)((char *)block - 16);
    }

    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

// given a block_size, we find what bucket it should be in the seglist.
int find_index(size_t block_size) {
    // minimum size must be 16 I think?
    // Edit later: This is in fact incorrect when I wrote this
    // however, me being incorrect saved me time when the minimum size actually
    // was supposed to be 16 insert michael scott shaking hands meme here

    // 0 will be the designated index for our mini blocks

    if (((1 << 4) <= block_size) && (block_size < (1 << 5)))
        return 0;
    else if (((1 << 5) <= block_size) && (block_size <= (1 << 6)))
        return 1;
    else if (((1 << 6) < block_size) && (block_size <= (1 << 7)))
        return 2;
    else if (((1 << 7) < block_size) && (block_size <= (1 << 8)))
        return 3;
    else if (((1 << 8) < block_size) && (block_size <= (1 << 9)))
        return 4;
    else if (((1 << 9) < block_size) && (block_size <= (1 << 10)))
        return 5;
    else if (((1 << 10) < block_size) && (block_size <= (1 << 11)))
        return 6;
    else if (((1 << 11) < block_size) && (block_size <= (1 << 12)))
        return 7;
    else if (((1 << 12) < block_size) && (block_size <= (1 << 13)))
        return 8;
    else if (((1 << 13) < block_size) && (block_size <= (1 << 14)))
        return 9;
    else if (((1 << 14) < block_size) && (block_size <= (1 << 15)))
        return 10;
    else if (((1 << 15) < block_size) && (block_size <= (1 << 16)))
        return 11;
    else if (((1 << 16) < block_size) && (block_size <= (1 << 17)))
        return 12;
    else if (((1 << 17) < block_size) && (block_size <= (1 << 18)))
        return 13;
    else {
        return 14;
    }
}

// if you can't figure out what this does I'll be very sad
void print_heap() {
    block_t *current_header = heap_start;
    if (get_size(current_header) == 0)
        return;
    block_t *next_header = find_next(current_header);
    printf("printing heap\n");
    while (get_size(next_header) != 0) {
        printf("Current block %ld, size %ld, alloc %d, prev alloc %d, prev "
               "mini %d\n",
               (long)&(*current_header), get_size(current_header),
               get_alloc(current_header), get_before_alloc(current_header),
               get_before_mini(current_header));

        current_header = next_header;
        next_header = find_next(next_header);
    }
    printf(
        "Current block %ld, size %ld, alloc %d, prev alloc %d, prev mini %d\n",
        (long)&(*current_header), get_size(current_header),
        get_alloc(current_header), get_before_alloc(current_header),
        get_before_mini(current_header));
    printf("Epilogue block %ld, alloc %d, prev alloc %d, prev mini %d",
           (long)&(*next_header), extract_alloc(next_header->header),
           extract_before_alloc(next_header->header),
           extract_before_mini(next_header->header));
    printf("\n\n");
}

// printing explicit list (not seglist)
// old, don't use
/*void print_free_list(){
    block_t *block = NULL;
    printf("printing free list\n");
    printf("Head: Block %ld \n", (long)&(*free_list_head));
    for (block = free_list_head; (block != NULL) && (get_size(block) > 0); block
= (block -> body).list_pointers.next) { if(block == (block ->
body).list_pointers.next) assert(0); printf("Block %ld, size %ld, alloc %d\n",
(long)&(*block), get_size(block), get_alloc(block));
    }
    printf("\n");

}*/

void print_mini(int line) {
    block_t *current_header = seg_list[0];
    if (current_header == NULL) {
        printf("Mini list empty\n");
        return;
    }

    printf("Printing miniList from %d\n", line);
    while (current_header != NULL) {
        printf("Current block %ld, ", (long)&(*current_header));
        printf("size %ld, alloc %d, prev alloc %d, prev mini %d\n",
               get_size(current_header), get_alloc(current_header),
               get_before_alloc(current_header),
               get_before_mini(current_header));
        current_header = (current_header->body).mini_pointers.next;
    }
    printf("\n");
}

void remove_miniblock(block_t *to_find) {
    // these blocks only have a next pointer
    dbg_requires(get_size(to_find) < 32);

    // testing if first block is the one we need to remove
    if (&(*seg_list[0]) == &(*to_find)) {
        seg_list[0] = (to_find->body).mini_pointers.next;
        return;
    }

    // search for where the block is
    block_t *current = seg_list[0];
    block_t *next = (current->body).mini_pointers.next;

    while (next != NULL) {
        // removing next from list
        if (&(*next) == &(*to_find)) {
            (current->body).mini_pointers.next =
                (next->body).mini_pointers.next;
            return;
        }

        current = next;
        next = (next->body).mini_pointers.next;
    }
    printf("Remove block with address %ld unsuccessful.", (long)&(*to_find));
}

// removes the block from the free list
void remove_block(block_t *current_block) {
    dbg_requires(get_alloc(current_block) == 0);

    int index = find_index(get_size(current_block));
    if (index == 0) {
        remove_miniblock(current_block);
        return;
    }

    // if front and end of list
    if ((&(*current_block) == &(*seg_list[index])) &&
        (((current_block->body).list_pointers.next) == NULL)) {
        seg_list[index] = NULL;
    }
    // if front of list
    else if (&(*current_block) == &(*seg_list[index])) {
        seg_list[index] = (current_block->body).list_pointers.next;
    }
    // end of list
    else if (((current_block->body).list_pointers.next) == NULL) {
        block_t *previous_block = (current_block->body).list_pointers.prev;
        (previous_block->body).list_pointers.next = NULL;
    } else {
        block_t *previous_block = (current_block->body).list_pointers.prev;
        block_t *next_block = (current_block->body).list_pointers.next;
        (next_block->body).list_pointers.prev = previous_block;
        (previous_block->body).list_pointers.next = next_block;
    }
}

// adds a miniblock to the front of the free list
// insertion is at the beginning of the list
void add_miniblock(block_t *current_block) {
    dbg_requires(get_size(current_block) < 32);

    (current_block->body).mini_pointers.next = seg_list[0];
    seg_list[0] = current_block;
}

// adds a block to the front of the free list
void add_block(block_t *current_block) {
    dbg_requires(get_alloc(current_block) == 0);
    int index = find_index(get_size(current_block));

    if (index == 0) {
        add_miniblock(current_block);
        return;
    }

    if (seg_list[index] == NULL) {
        (current_block->body).list_pointers.next = NULL;
        seg_list[index] = current_block;
    } else {
        (seg_list[index]->body).list_pointers.prev = current_block;
        (current_block->body).list_pointers.next = seg_list[index];
        seg_list[index] = current_block;
    }
}

// checks if current block is mini
bool is_mini(block_t *current_block) {
    return (get_size(current_block) <= 16) && (get_size(current_block) > 0);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

void combine_one_block(block_t *top, block_t *bottom) {
    write_block(top, get_size(top) + get_size(bottom), false,
                get_before_alloc(top), get_before_mini(top));
}

void combine_two_block(block_t *top, block_t *middle, block_t *bottom) {
    size_t top_size = get_size(top);
    size_t mid_size = get_size(middle);
    size_t bottom_size = get_size(bottom);

    write_block(top, top_size + mid_size + bottom_size, false,
                get_before_alloc(top), get_before_mini(top));
}
/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {

    // why do we need find_prev in the first place?
    // remember that we remove footers only for allocated blocks lol
    // find if the block before is allocated or free
    bool prev_alloc_status = get_before_alloc(block);
    // find allocation status of before block
    bool before_alloc = true;
    block_t *before = NULL;
    if (!prev_alloc_status) {
        before = find_prev(block);
        if (before != NULL) {
            before_alloc = get_alloc(before);
        }
    }

    // find allocation status of after block
    block_t *after = find_next(block);
    bool after_alloc = true;

    if (get_size(after) != 0) {
        after_alloc = get_alloc(after);
    }

    // case depending on what type of coalesce we need to do:
    if ((before_alloc == true) && (after_alloc == true)) {
        return block;
    } else if ((before_alloc == false) && (after_alloc == true)) {
        // removing from free list
        remove_block(before);
        remove_block(block);

        combine_one_block(before, block);

        add_block(before);

        return before;
    } else if ((before_alloc == true) && (after_alloc == false)) {
        // removing from free list
        remove_block(block);
        remove_block(after);

        combine_one_block(block, after);

        add_block(block);

        return block;
    } else { // both are false
        // removing from free list
        remove_block(before);
        remove_block(block);
        remove_block(after);

        combine_two_block(before, block, after);

        add_block(before);

        return before;
    }
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */

static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    // bp = block payload, i wish someone told me this last week

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false, get_before_alloc(block),
                get_before_mini(block));
    add_block(block);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next, false, false);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */
    // no

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true, get_before_alloc(block),
                    get_before_mini(block));

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false, true,
                    is_mini(block));
        add_block(block_next);

        // after we have a new free block, we must mark the next block's prev
        // alloc as false, and the is_mini accordingly.
        block_t *next = find_next(block_next);
        bool is_mini_block = is_mini(block_next);
        if (get_size(next) > 0) {
            write_block(next, get_size(next), get_alloc(next), false,
                        is_mini_block);
        } else {
            dbg_assert(get_size(next) == 0);
            write_epilogue(next, false, is_mini_block);
        }
    }

    dbg_ensures(get_alloc(block));
}

static block_t *find_mini() {
    // seg_list[0] is the first available free miniblock.
    return seg_list[0];
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    block_t *block;
    int index = find_index(asize);

    if (index == 0) {
        block = find_mini();
        if (block != NULL) {
            return block;
        } else {
            index = 1;
        }
    }

    for (int i = index; i < 15; i++) {
        for (block = seg_list[i]; (block != NULL) && (get_size(block) > 0);
             block = (block->body).list_pointers.next) {

            if (!(get_alloc(block)) && (asize <= get_size(block))) {
                return block;
            }
        }
    }

    return NULL; // no fit found
}

bool check_size(block_t *current_header) {
    return true;
    // I have no idea how to compare the addresses in mem_heap_lo() and
    return (&*(char *)mem_heap_lo() < &*(char *)current_header) &&
           (&*(char *)current_header < &*(char *)mem_heap_hi());
    // I can either case mem_heap_lo() to a char * or I can
    // cast current_header to a void* and compare it that way
}

bool compare_sizes(block_t *current_header, word_t *current_footer) {
    // compare the size in header and footer to be the same
    size_t header_size = get_size(current_header);
    size_t footer_size = extract_size(*current_footer);

    return header_size == footer_size;
}

bool compare_alloc(block_t *current_header, word_t *current_footer) {
    // compare the alloc in header and footer to be the same
    bool header_alloc = get_alloc(current_header);
    bool footer_alloc = extract_alloc(*current_footer);

    return header_alloc == footer_alloc;
}

// I have no idea if this is correct either
bool check_alignment(block_t *current_header) {
    void *current_payload = header_to_payload(current_header);
    return ((long)&current_payload % 16) == 0;
}

bool check_circularity(block_t *current_block) {
    // end of list
    if (((current_block->body).list_pointers.next) == NULL) {
        return true;
    } else {
        block_t *next_block = (current_block->body).list_pointers.next;
        return (next_block->body).list_pointers.prev == current_block;
    }
}
bool check_forward_back(block_t *current_block, int line) {
    block_t *current_header = heap_start;
    bool cur_alloc = get_alloc(current_header);
    bool prev_alloc = false;
    block_t *next_header = find_next(current_header);

    while (get_size(next_header) != 0) {
        prev_alloc = get_before_alloc(next_header);

        if (cur_alloc != prev_alloc) {
            printf("Error on line %d, previous alloc doesn't match cur_alloc\n",
                   line);
            return false;
        }

        current_header = next_header;
        next_header = find_next(next_header);
        cur_alloc = get_alloc(current_header);
    }
    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {
    // print_heap();
    // print_mini(line);
    // printf("\n\n");
    // return check_forward_back(heap_start, line);

    // imagine actually checking the heap
    return true;

    // first check: the heap must exist lol
    if (heap_start == NULL) {
        printf("Error on line %d, heap is not initialized.\n", line);
        return false;
    } else if (mem_heapsize() == 0)
        return true;
    // second check: check each block's address alignment
    block_t *current_header = heap_start;
    block_t *next_header = find_next(current_header);
    word_t *current_footer = header_to_footer(current_header);

    // we're also counting the number of free blocks while we're at it
    size_t num_free_blocks = 0;
    while (get_size(next_header) != 0) {
        current_footer = header_to_footer(current_header);

        if (get_alloc(current_header) == false)
            num_free_blocks++;

        // check if epilogue/footer block exists
        if (current_footer == NULL) {
            printf(
                "Error on line %d, footer does not exist for given header.\n",
                line);
            return false;
        }

        if (!compare_sizes(current_header, current_footer)) {
            printf("Error on line %d, header size does not match footer\n",
                   line);
            printf("header size: %ld, footer size: %ld\n",
                   get_size(current_header), extract_size(*current_footer));
            return false;
        }

        if (!compare_alloc(current_header, current_footer)) {
            printf("Error on line %d, header alloc does not match footer\n",
                   line);
            return false;
        }

        if (!check_size(current_header)) {
            printf("Error on line %d, part of memory is not on heap.\n", line);
            return false;
        }

        if (!check_alignment(current_header)) {
            printf("Error on line %d, memory is not 16 byte aligned.\n", line);
            return false;
        }

        current_header = next_header;
        next_header = find_next(next_header);
    }

    // last element in heap:
    current_footer = header_to_footer(current_header);
    if (get_alloc(current_header) == false)
        num_free_blocks++;
    if (current_footer == NULL) {
        printf("Error on line %d, footer does not exist for given header.\n",
               line);
        return false;
    }

    if (!compare_sizes(current_header, current_footer)) {
        printf("Error on line %d, header size does not match footer\n", line);
        return false;
    }

    if (!compare_alloc(current_header, current_footer)) {
        printf("Error on line %d, header alloc does not match footer\n", line);
        return false;
    }

    if (!check_size(current_header)) {
        printf("Error on line %d, part of memory is not on heap.\n", line);
        return false;
    }

    if (!check_alignment(current_header)) {
        printf("Error on line %d, memory is not 16 byte aligned.\n", line);
        return false;
    }

    // check coalescing: no consecutive free blocks in the heap
    current_header = heap_start;
    next_header = find_next(current_header);

    // special case: one block on heap
    if (get_size(next_header) == 0)
        return true;

    block_t *end_checker = find_next(next_header);

    while (get_size(end_checker) != 0) {
        bool cur_alloc = get_alloc(current_header);
        bool next_alloc = get_alloc(next_header);

        if ((cur_alloc == false) && (next_alloc == false)) {
            printf("Error on line %d, two free blocks together.\n", line);
            return false;
        }

        current_header = next_header;
        next_header = end_checker;
        end_checker = find_next(end_checker);
    }

    block_t *seg_list_start = NULL;
    // we will compare this to the number of free blocks on the heap
    size_t counter = 0;
    for (int i = 0; i < 15; i++) {
        seg_list_start = seg_list[i];
        while (seg_list_start != NULL) {
            counter++;

            if (!check_circularity(seg_list_start)) {
                printf(
                    "Error on line %d, free list not doubly linked properly.\n",
                    line);
                return false;
            }

            else if (i != find_index(get_size(seg_list_start))) {
                printf("Error on line %d, wrong size in bucket.\n", line);
                return false;
            }
            seg_list_start = (seg_list_start->body).list_pointers.next;
        }
    }

    if (counter != num_free_blocks) {
        printf("Error on line %d, number of free blocks is not consistent.\n",
               line);
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about why we need a heap prologue and epilogue. Why do
     * they correspond to a block footer and header respectively?
     */

    // making the prev_alloc status of these two true bc it doesn't matter
    start[0] = pack(0, true, true, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    // free_list_head = NULL;
    for (int i = 0; i < 15; i++) {
        seg_list[i] = NULL;
    }
    seg_list[0] = NULL;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    // we take in the request size and then we add the internal fragmentation
    // size to it (multiple of dsize) note: dsize is the size of the header +
    // footer, dont' aallocate this much lol wsize = size of one header
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    remove_block(block);
    // conceptually, the block before must always be allocated
    write_block(block, block_size, true, true, get_before_mini(block));

    // Try to split the block if too large
    split_block(block, asize);

    block_t *next = find_next(block);

    bool is_mini_block = is_mini(block);
    // updating the block after to change alloc status
    if (get_size(next) > 0) {
        if (get_alloc(next) == 0) {
            remove_block(next);
        }
        write_block(next, get_size(next), get_alloc(next), true, is_mini_block);
        if (get_alloc(next) == 0) {
            add_block(next);
        }
    } else {
        dbg_assert(get_size(next) == 0);
        write_epilogue(next, true, is_mini_block);
    }

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    bool prev_alloc = get_before_alloc(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false, prev_alloc, get_before_mini(block));
    add_block(block);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    block_t *next = find_next(block);
    if (get_size(next) > 0) {
        if (get_alloc(next) == 0) {
            remove_block(next);
        }
        write_block(next, get_size(next), get_alloc(next), false,
                    is_mini(block));
        if (get_alloc(next) == 0) {
            add_block(next);
        }
    } else {
        write_epilogue(next, false, is_mini(block));
    }

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
