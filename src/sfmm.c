/**
 * Do not submit your assignment with a main function in this file.
 * If you submit with a main function in this file, you will get a zero.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "debug.h"
#include "sfmm.h"


static int total_mem = 0;
static int available_mem = 0;
static sf_block *prologue = 0;
static sf_block *epilogue = 0;
static void init_lists();
static void add_block(sf_block* b);
static void add_to_freelist(sf_block *head, sf_block *node);
static void remove_freelist(sf_block *node);
static void split_block(sf_block* b, int size);
static sf_block* extend_page(int size);
static int check_invalid_pointer(void  *p);
static void add_to_quicklist(sf_block *b, int index);
static void pop_quicklist(int index);
static void coellesce_prev_next(sf_block *b);
static double total_payload = 0;
static double max_total_payload = 0;
static double total_block = 0;

void *sf_malloc(sf_size_t size) {
    if(size == 0){
        return NULL;
    }

    void* heap_cursor = 0;
    if(sf_mem_start() == sf_mem_end()){
        if(sf_mem_grow() == NULL){
            sf_errno = ENOMEM;
            return NULL;
        }
        total_mem = 1024;


        //setting prologue
        prologue = (sf_block*)sf_mem_start();
        prologue->header = 36;
        prologue->header ^= MAGIC;

        //setting epilogue
        epilogue = (sf_block*)((char*)sf_mem_end() - 16);
        epilogue->header = 4 ^ MAGIC;

        //initialize lists
        init_lists();

        available_mem =  total_mem - 32 - 8 - 8;

        heap_cursor = (char*)sf_mem_start() + 32;

        sf_block *block = (sf_block*)heap_cursor;

        //alloc = 0, prevalloc = 1, inqcklist = 0
        block->header += available_mem + 2;
        block->header ^= MAGIC;

        //set footer
        epilogue->prev_footer += available_mem + 2;
        epilogue->prev_footer ^= MAGIC;

        //available_mem -= blocksize;
        //printf("%i\n", available_mem);



        //add block to list
        add_block(block);
    }


    //check quick lists
    int blocksize = size + 8;
    while(blocksize%16 != 0 || blocksize < 32){
        blocksize++;
    }
    int quick_list_index = (blocksize - 32)/16;


    sf_block **first = &sf_quick_lists[quick_list_index].first;
    if(quick_list_index < NUM_QUICK_LISTS && *first){

        //add size
        (*first)->header ^= MAGIC;
        (*first)->header += (((uint64_t)size) << 32) - 1;
        (*first)->header ^= MAGIC;

        total_payload += ((*first)->header ^ MAGIC) >> 32;
        max_total_payload += total_payload;
        total_block += (int)(((*first)->header ^ MAGIC) & ~0xF);

        char *payload = (*first)->body.payload;
        pop_quicklist(quick_list_index);
        //sf_show_heap();
        return payload;
    }

    //check free lists
    int list_size = 32;
    for(int i = 0; i < NUM_FREE_LISTS;i++){
        if(i != 0) list_size = 32* (2 << (i - 1));

        if(size <= list_size){
            //check list

            sf_block *head = &sf_free_list_heads[i];
            sf_block *cursor = head->body.links.next;

            while(cursor != head){
                int fsize = (cursor->header ^ MAGIC) & ~0xF;
                //free blocks found
                if((size + 8) <= fsize){
                    //allocate block

                    //remove block from free list
                    remove_freelist(cursor);

                    //split and allocate block
                    split_block(cursor, size);

                    //show info
                    //printf("%d\n", available_mem);
                    //sf_show_heap();

                    total_payload += (cursor->header ^ MAGIC) >> 32;
                    max_total_payload += total_payload;
                    total_block += (int)((cursor->header ^ MAGIC) & ~0xF);
                    return cursor->body.payload;
                }
                cursor = cursor->body.links.next;
            }
        }
    }

    sf_block* new_block = extend_page(size);

    //add free block to proper list
    remove_freelist(new_block);
    add_block(new_block);

    if(sf_errno == ENOMEM){
        return NULL;
    }

    //show info
    //printf("%d\n", available_mem);
    //sf_show_heap();
    return sf_malloc(size);
}

void add_block(sf_block* b){
    int size = (b->header ^ MAGIC) & ~0xF;
    //printf("%d\n", size);


    int upper = 32;
    for(int i = 0; i < NUM_FREE_LISTS;i++){
        if(i != 0) upper = 32 * (2 << (i - 1));

        if(size <= upper || (i == NUM_FREE_LISTS - 1)){
            //printf("%d\n",upper);
            add_to_freelist(&sf_free_list_heads[i], b);
            break;
        }
    }
}

void add_to_freelist(sf_block *head, sf_block *node){
    node->body.links.next = head->body.links.next;
    head->body.links.next = node;
    node->body.links.prev = head;
    node->body.links.next->body.links.prev = node;
}
void remove_freelist(sf_block *node){
    sf_block *prev = node->body.links.prev;
    sf_block *next = node->body.links.next;

    if(!prev || !next){
        return;
    }

    prev->body.links.next = next;
    next->body.links.prev = prev;

    node->body.links.next = 0;
    node->body.links.prev = 0;
}

void split_block(sf_block* b, int size){
    b->header ^= MAGIC;
    int prealloc = b->header & PREV_BLOCK_ALLOCATED;
    int oldsize = b->header & ~0xF;

    int blocksize = size + 8;
    while(blocksize%16 != 0 || blocksize < 32){
        blocksize++;
    }

    //check splinter
    if(oldsize - blocksize < 32){
        // payloadsize = size, block size = header + footer + size + padding
        b->header = ((uint64_t)size) << 32;
        b->header += oldsize + 4 + prealloc;

        sf_block *next_header = (sf_block*)((char*)b + oldsize);
        next_header->header ^= MAGIC;
        next_header->header |= 2;
        next_header->header ^= MAGIC;

        available_mem -= oldsize;

    } else {
        b->header = ((uint64_t)size) << 32;
        b->header += blocksize + 4 + prealloc;

        //set new free block
        sf_block *next_header = (sf_block*)((char*)b + blocksize);
        next_header->header = (oldsize - blocksize) + 2;
        int nsize = next_header->header & ~0xF;
        next_header->header ^= MAGIC;

        //set footer
        sf_block *next_block =(sf_block*)((char*)next_header + nsize);
        next_block->prev_footer = next_header->header;

        //add new block to list
        add_block(next_header);

        available_mem -= blocksize;
    }

    b->header ^= MAGIC;
}

void init_lists(){
    for(int i = 0; i < NUM_FREE_LISTS;i++){
        sf_free_list_heads[i].body.links.next = &sf_free_list_heads[i];
        sf_free_list_heads[i].body.links.prev = &sf_free_list_heads[i];
    }

    for(int i = 0; i < NUM_QUICK_LISTS;i++){
        sf_quick_lists[i].first = 0;
        sf_quick_lists[i].length = 0;
    }
}

//returns bigger free block
sf_block* extend_page(int size){
    int new_block_size = 0;

    char prev_allocated = (epilogue->header ^ MAGIC) & PREV_BLOCK_ALLOCATED;


    //if last block is a free block
    if( !prev_allocated ){
        //size of previous freeblock
        int prev_size = ((epilogue->prev_footer ^ MAGIC) & ~0xF);

        new_block_size += prev_size;

        //previous free block
        sf_block *prev_block = (sf_block*)((char*)epilogue - prev_size);

        //get new mem
        while(new_block_size < (size + 8)){
            if(sf_mem_grow() == NULL){
                sf_errno = ENOMEM;
                break;
            }
            new_block_size += 1024;
            total_mem += 1024;
            available_mem += 1024;
        }


        prev_block->header ^= MAGIC;
        prev_block->header += (new_block_size - prev_size);
        prev_block->header ^= MAGIC;


        //setting epilogue
        epilogue = (sf_block*)( (char*)sf_mem_end() - 16);
        epilogue->header = 4 ^ MAGIC;
        epilogue->prev_footer = prev_block->header;

        return prev_block;
    } else {

        while(new_block_size < (size + 8)){
            if(sf_mem_grow() == NULL){
                sf_errno = ENOMEM;
                break;
            }
            new_block_size += 1024;
            total_mem += 1024;
            available_mem += 1024;
        }

        //set new block size, pal = 1
        sf_block *new_block = epilogue;
        new_block->header ^= MAGIC;
        new_block->header = new_block_size + 2;
        new_block->header ^= MAGIC;

        //setting epilogue
        epilogue = (sf_block*)( (char*)sf_mem_end() - 16);
        epilogue->header = 4 ^ MAGIC;
        epilogue->prev_footer = new_block->header;

        return new_block;
    }
}

void sf_free(void *pp) {
    if(!check_invalid_pointer(pp)){
        abort();
    }
    sf_block *block = (sf_block*)((char*)pp - 16);
    int block_size = (block->header ^ MAGIC) & ~0xF;
    int quick_list_index = (block_size - 32)/16;

    total_payload -= (block->header ^ MAGIC) >> 32;
    total_block -= block_size;

    //if block can go in quicklist
    if(quick_list_index < NUM_QUICK_LISTS){

        block->header ^= MAGIC;
        //clear payload
        block->header &= 0x00000000FFFFFFFF;
        //set inquicklist 1
        block->header += 1;
        block->header ^= MAGIC;

        int length = sf_quick_lists[quick_list_index].length;
        if(length >= QUICK_LIST_MAX){

            sf_block **qcklist = &sf_quick_lists[quick_list_index].first;
            for(int i = 0; i < QUICK_LIST_MAX;i++){
                    (*qcklist)->header ^= MAGIC;
                    //alloc 0, qcklist 0
                    (*qcklist)->header -= 5;
                    int size = (*qcklist)->header & ~0xF;
                    (*qcklist)->header ^= MAGIC;

                    //set footer
                    sf_block *next = (sf_block*)((char*)(*qcklist) + size);
                    next->prev_footer = (*qcklist)->header;

                    // coellesce and add
                    coellesce_prev_next(*qcklist);
                    if(i == QUICK_LIST_MAX - 1){
                        add_block(*qcklist);
                    }


                    *qcklist = (*qcklist)->body.links.next;
            }

            //set pal to 0
            block->header ^= MAGIC;
            block->header -= PREV_BLOCK_ALLOCATED;
            block->header ^= MAGIC;

            //add new first node
            sf_quick_lists[quick_list_index].first = 0;
            sf_quick_lists[quick_list_index].length = 1;
            add_to_quicklist(block, quick_list_index);

        } else {
            //add to quick list
            add_to_quicklist(block, quick_list_index);
            sf_quick_lists[quick_list_index].length++;
        }

    } else {
        block->header ^= MAGIC;
        //clear payload
        block->header &= 0x00000000FFFFFFFF;
        //set alloc 0
        block->header -= 4;
        block->header ^= MAGIC;


        //set next pal 0 and footer
        sf_block *next_block = (sf_block*)((char*)block + block_size);
        next_block->prev_footer = block->header;
        next_block->header ^= MAGIC;
        next_block->header -= 2;
        next_block->header ^= MAGIC;


        coellesce_prev_next(block);

        add_block(block);
    }

    //sf_show_heap();
}

void coellesce_prev_next(sf_block *block){
    int block_size = (block->header ^ MAGIC) & ~0xF;

    //coellesce previous
    if(!((block->header ^ MAGIC) & PREV_BLOCK_ALLOCATED)){
        int prev_block_size = (block->prev_footer ^ MAGIC) & ~0xF;

        block = (sf_block*)( (char*)block - prev_block_size);
        remove_freelist(block);

        block->header ^= MAGIC;
        block->header += block_size;
        block_size += prev_block_size;
        block->header ^= MAGIC;
    }

    //coellesce next
    sf_block *next_block = (sf_block*)( (char*)block + block_size);
    if(!((next_block->header ^ MAGIC) & THIS_BLOCK_ALLOCATED)){
        int next_block_size = (next_block->header ^ MAGIC) & ~0xF;
        remove_freelist(next_block);

        block->header ^= MAGIC;
        block->header += next_block_size;
        block_size += next_block_size;
        block->header ^= MAGIC;
    }

    //set footer
    next_block = (sf_block*)( (char*)block + block_size);
    next_block->prev_footer = block->header;
}

void add_to_quicklist(sf_block *b, int index){
    sf_block **first = &sf_quick_lists[index].first;
    if(!*first){
        b->body.links.next = NULL;
        *first = b;
    } else {
        b->body.links.next = *first;
        *first = b;
    }
}

void pop_quicklist(int index){
    if(sf_quick_lists[index].first){
        sf_quick_lists[index].length--;
        sf_quick_lists[index].first = sf_quick_lists[index].first->body.links.next;
    }
}

void *sf_realloc(void *pp, sf_size_t rsize) {
    if(!check_invalid_pointer(pp)){
        sf_errno = EINVAL;
        return NULL;
    }

    sf_block *block = (sf_block*)((char*)pp - 16);
    int payload_size = (block->header ^ MAGIC) >> 32;

    if(rsize == 0){
        sf_free(pp);
        return NULL;
    }

    //larger size
    if(payload_size < rsize){
        sf_free(pp);

        sf_block *new_block = (sf_block*)((char*)sf_malloc(rsize) - 16);

        if(!new_block){
            return NULL;
        }

        //copy payload
        memcpy(new_block->body.payload, block->body.payload, rsize);

        return new_block->body.payload;
    }


    //smaller size
    if(payload_size > rsize){
        //splinter

        total_payload -= (block->header ^ MAGIC) >> 32;
        total_block -= (int)((block->header ^ MAGIC) & ~0xF);

        split_block(block, rsize);

        int block_size = (block->header ^ MAGIC) & ~0xF;

        total_payload += (block->header ^ MAGIC) >> 32;
        total_block += block_size;

        //coellesce split block
        sf_block *split_block = (sf_block*)((char*)block + block_size);
        coellesce_prev_next(split_block);

        //sf_show_heap();
        return block->body.payload;
    }

    //same size
    if(payload_size == rsize){
        return pp;
    }

    return 0;
}

double sf_internal_fragmentation() {

    if(!total_block){
        return 0.0;
    }

    return total_payload/total_block;
}

double sf_peak_utilization() {
    double heap_size = sf_mem_end() - sf_mem_start();

    if(heap_size == 0.0){
        return 0.0;
    } else {
        return max_total_payload/heap_size;
    }
}

//returns 0 if invalid pointer
int check_invalid_pointer(void  *p){

    //pointer null
    if(!p){
        return 0;
    }

    //check alligned
    if((uintptr_t)p % 16 != 0){
        return 0;
    }

    sf_block *pointer_block = (sf_block*)((char*)p - 16);

    sf_header pointer_header = pointer_block->header ^ MAGIC;

    //check block size
    int block_size = pointer_header & ~0xF;
    if(block_size < 32 || (block_size % 16 != 0)){
        return 0;
    }

    //check if not allocated
    int alloc = pointer_header & THIS_BLOCK_ALLOCATED;
    if(!alloc){
        return 0;
    }

    //check prevalloc 0 but alloc 1 in prev block
    int prevalloc = pointer_header & PREV_BLOCK_ALLOCATED;
    if(!prevalloc){
        //if previous block alloc 1
        if( (pointer_block->prev_footer ^ MAGIC) & THIS_BLOCK_ALLOCATED ){
            return 0;
        }
    }

    //check if in heap
    sf_block *next_block = (sf_block*)((char*)pointer_block + block_size);
    if( (&pointer_block->header < (sf_header*)sf_mem_start()) || (&next_block->prev_footer > (sf_footer*) sf_mem_end())){
        return 0;
    }
    return 1;
}

