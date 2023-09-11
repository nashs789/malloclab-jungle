/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Team_7",
    /* First member's full name */
    "Lee In Bok",
    /* First member's email address */
    "bbock1214@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basize constants and macros */
#define WSIZE 4                                                             /* Word and header/footer size (bytes) */
#define DSIZE 8                                                             /* Double word size (bytes)*/
#define CHUNKSIZE (1 << 12)                                                 /* Extend heap by this amount (bytes) == 4096 */
#define MAX(x, y) ( (x) > (y) ? (x) : (y))                                  /* 최대 값 확인*/
#define PACK(size, alloc) ((size) | (alloc))                                /* Pack a size and allocated bit into a word */
#define GET(p) (*(unsigned int *)(p))                                       /* Read a word at address p / 4 Byte 형태로 메모리에서 데이터를 읽겠다. */
#define PUT(p, val) (*(unsigned int *)(p) = (val))                          /* write a word at address p */
/* 
0x7을 Not 연산자 수행시 이진수로 1000(2) 이고, 특정 비트들(맨 오른쪽) 0으로 만들어 남은 비트들이 원래 역할을 수행할 수 있도록 해준다. 
사용하는 포인터 주소에 마지막 비트에 0: Free 1: Allocated 정보를 저장하게 했기 때문에 &연산으로 뒤의 3자리 비트를 복구 시키는 것

어떻게 비트로 데이터 사이즈를 알 수 있을까? (3비트 기준 2^3 가지의 비트 크기 단위를 설정 가능하다.)
Example)
000: 2^0 (1 Bytes)
001: 2^1 (2 Bytes)
010: 2^2 (4 Bytes)
011: 2^3 (8 Bytes)
100: 2^4 (16 Bytes)
101: 2^5 (32 Bytes)
110: 2^6 (64 Bytes)
111: 2^7 (128 Bytes)
*/
#define GET_SIZE(p) (GET(p) & ~0x7)                                         /* Read the size from address p */
/* 할당 여부를 받는 매크로 함수: 0 or 1만 결과 값으로 나오게 되어있음 */
#define GET_ALLOC(p) (GET(p) & 0x1)                                         /* Read Allocated fields from address p */
/* 
                              BP
|----Footer----|----Header----|----Block----|----Footer----|
|----4 Byte----|----4 Byte----|----Block----|----4 Byte----| 
*/
#define HDRP(bp) ((char *)(bp) - WSIZE)                                     /* Given block ptr bp, compute address of its header */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)                /* Given block ptr bp, compute address of its footer */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))     /* Given block ptr bp, compute address of next blocks */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))     /* Given block ptr bp, compute address of previous blocks */

typedef unsigned long dword_t;
typedef char* byte_p;

static void* g_next_p;

static void *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *ptr);
static void *find_fit(size_t asize);
static void place(void *ptr, size_t asize);
static void* first_fit(size_t asize);
static void* next_fit(size_t asize);
size_t *resize(size_t size);
dword_t __offset(void *p);

static size_t __get_size(void *p) { return GET_SIZE(p); }
static bool __gel_alloc(void *p) { return GET_ALLOC(p); }
static byte_p __get_h_p(void *bp) { return HDRP(bp); }
static byte_p __get_f_p(void *bp) { return FTRP(bp); }
static void* __get_next_p(void *bp) { return NEXT_BLKP(bp); }
static void* __get_prev_p(void *bp) { return PREV_BLKP(bp); }

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void){
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1){
        return -1;   
    }

    PUT(heap_listp, 0);                            /* Alignment padding */
    /* Prologue block은 Header + Footer (8 Bytes)로 구성된다. */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    /* Epilogue block은 Header(4 Bytes)로 구성된다. + Prologue, Epilogue는 초기화 과정에서 생성되며 절대 반환하지 않음*/
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);
    g_next_p = heap_listp;
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL){
        return -1;
    }
    
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    /* Ignore spurious requests */
    if (size == 0) {
        return NULL;
    } 

    size_t asize = resize(size);    /* Adjusted block size */
    size_t extendsize;              /* Amount to extend heap if no fit */
    void *bp;

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        
        return bp; 
    }
    
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }   

    place(bp, asize);

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* 최소 사이즈 만족도 하지 못하는 경우 최소 사이즈로 변환 */
size_t *resize(size_t size) {
    /*
        Adjust block size to include overhead and alignment reqs.
        
        Examle) size = 20
        asize = DSIZE * ((20 + DSIZE + (DSIZE - 1)) / DSIZE)
        asize = DSIZE * ((20 + 8 + 7) / 8)
        asize = DSIZE * (35 / 8)
        asize = DSIZE * 4
        asize = 32
    */
    
    return size <= DSIZE ? 2 * DSIZE : DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    size_t cur_size = GET_SIZE(HDRP(ptr));
    size_t nxt_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    size_t prv_size = GET_SIZE(FTRP(PREV_BLKP(ptr)));
    bool isNxtAlloc = GET_ALLOC(HDRP(ptr));
    bool isPrvAlloc = GET_ALLOC(FTRP(ptr));
    dword_t packed = NULL;
    size = resize(size);

    // 과연 케이스 3개를 확인하면서 발생하는 overhead가 memcpy보다 utilization이 높을까?
    if(!isPrvAlloc && isNxtAlloc && size <= cur_size + prv_size - DSIZE){
        size += prv_size;

        PUT(FTRP(ptr), PACK(cur_size, 0));
        PUT(FTRP(PREV_BLKP(ptr)), PACK(size, 1));

        return ptr;
    } else if(isPrvAlloc && !isNxtAlloc && size <= cur_size + nxt_size - DSIZE){
        size += nxt_size;

        PUT(HDRP(ptr), PACK(cur_size, 0));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(size, 1));

        return ptr;
    } else if(!isNxtAlloc && !isPrvAlloc && size <= cur_size + nxt_size + prv_size - DSIZE){
        PUT(FTRP(ptr), PACK(cur_size, 0));
        PUT(FTRP(PREV_BLKP(ptr)), PACK(size, 1));
        PUT(HDRP(ptr), PACK(cur_size, 0));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(size, 1));

        return ptr;
    }

    if (ptr == NULL) {
        return mm_malloc(size);
    }

    if (size <= 0) {
        mm_free(ptr);
        return 0;
    } 

    void *new_ptr = mm_malloc(size);
    
    if (new_ptr == NULL) {
        return NULL;
    }

    size_t csize = GET_SIZE(HDRP(ptr)) - DSIZE;

    if (size < csize) { // 재할당 요청에 들어온 크기보다, 기존 block의 크기가 크다면
        csize = size; // 기존 block의 크기를 요청에 들어온 크기 만큼으로 줄인다.
    }

    /*
        function   : memcpy(destination, source, size_t)
        path       : <string.h>
        parameter  : ⚙︎ destination: 복사할 데이터가 위치할 메모리주소를 가르키는 포인터
                     ⚙︎ source     : 복사할 데이터가 위치한 메모리주소를 가르키는 포인터
                     ⚙︎ size_t     : 복사할 데이터의 길이 (Bytes)
        description: source에 있는 원본 데이터를 size_t만큼 복사해 destination 주소로 복사
        caution    : ⚙︎ size_t 가 char* 인 경우에는 문자열의 끝을 알리는 "\0" 까지 복사해야 하기 때문에 길이 + 1을 해준다.
                     ⚙︎ desination과 source의 메모리 주소는 겹치면 안된다.
    */      
    memcpy(new_ptr, ptr, csize); // ptr 위치에서 csize만큼의 크기를 new_ptr의 위치에 복사함
    mm_free(ptr); // 기존 ptr의 메모리는 할당 해제해줌

    return new_ptr;
}

/* 초기화 & 적당한 Fit을 찾지 못했을 때 호출되는 함수 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    /* 짝수개의 워드를 유지하기 위해서 조건식 사용 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    /* 의문) 이전 에필로그 block은 초기화 안해주나? -> 어차피 header의 위치가 되면서 free block이 되니까 괜찮은걸로 보임 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 - 둘 다 할당되어있는 케이스 */
        return bp;
    } else if(prev_alloc && !next_alloc) {     /* Case 2 - 앞 Alloc / 뒤 Free */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 1. Get the previous block's size from its Header

        PUT(HDRP(bp), PACK(size, 0));          // 2. Set Header
        PUT(FTRP(bp), PACK(size, 0));          // 3. Set Footer
    } else if(!prev_alloc && next_alloc) {     /* Case 3 - 앞 Free / 뒤 Alloc */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {                                   /* Case 4 - 앞 Free / 뒤 Free */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    g_next_p = bp;
    return bp;
}

static void* find_fit(size_t asize) {
    //first_fit(asize);
    next_fit(asize);
}

static void* next_fit(size_t asize) {
    void *bp;

    for(bp = g_next_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))){
            g_next_p = bp;
            return bp;
        }
    }

    for(bp = heap_listp; bp < g_next_p; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))){
            g_next_p = bp;
            return bp;
        }
    }

    return NULL;
}

static void* first_fit(size_t asize) {
    void *bp;

    // bp의 초기 값은 힙 메모리의 시작 값이며, 에필로그의 값에 도달시 종료하게 된다.
    for(bp = (char *)heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        // block이 'allocated' 상태가 아니며 && 요청한 asize 크기보다 큰 경우
        if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }

    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    /* 현재 block에서 할당할 block의 크기를 뺀 값을 free block 만들기 충분한 공간인지 확인 */
    /* 
        ⚙︎ 2 * DSIZE 인 이유: 
        1. 최소 공간: header와 footer 각각의 공간을 나타내는 최소의 크기
        2. 분할 조건: 위와 같이 최소 정렬 최소 사이즈를 맞춰주면 할당 후에도 정렬 조건에 맞는 Free 공간이 남아 있음을 보장
     */
    if ((csize - asize) >= (2 * DSIZE)) {
        // 현 메모리 block header, footer에서 asize 크기의 'allocate' block으로 설정
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 현 메모리 다음 block header, footer asize 크기의 남은 공간의 크기와 'free' block으로 설정
        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
    } else{     // 남은 공간이 충분하지 않은 경우
        // 현재 메모리 block의 header, footer 모두 'allocated' 로 설정한다.
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// ========================================================

dword_t __offset(void *p){
    return (dword_t)((byte_p)p - (byte_p)heap_listp);
}