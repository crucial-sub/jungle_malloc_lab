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

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Krafton Jungle",
    /* First member's full name */
    "Jungsub Park",
    /* First member's email address */
    "jssub940@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* Basic constants and macros */
#define WSIZE       4        /* malloc lab 과제 기준 1워드 크기를 4바이트로 정의 => 헤더와 푸터의 크기로 사용 */
#define DSIZE       8        /* 더블 워드의 크기는 8바이트 => 메모리 정렬의 기본 단위로 사용 */
#define CHUNKSIZE  (1<<12)   /* 힙 공간이 부족할 때, sbrk를 통해 추가로 요청할 메모리의 기본 크기 (2^12 = 4096바이트 ) */

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* 헤더와 푸터 관리를 위한 툴 PACK, GET, PUT */
/* 블록의 크기 정보와 할당 여부 비트를 하나의 4바이트 워드에 합쳐주는 역할 */
#define PACK(size, alloc) ((size) | (alloc))

/* 특정 메모리 주소 p에 있는 4바이트 워드 값을 읽거나(GET) 쓰는(PUT) 매크로 */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))
/* PUT과 PACK 혼합 사용 예시 */
/* PUT(p, PACK(size, 1)): p가 가리키는 주소(거의 헤더 혹은 푸터)에 
"이 블록의 크기는 size이며 할당된 상태입니다." 라는 정보가 담긴 하나의 워드(4바이트)짜리 값을 넣는다는 뜻 */

/* PACK으로 합쳐놓은 값에서 다시 크기 정보와 할당 비트를 분리해내는 역할 */
#define GET_SIZE(p)  (GET(p) & ~0x7) /* ~0x7은 이진수로 ...11111000 => &연산 시 마지막 3비트가 강제로 0이 되면서 순수한 블록 크기만 남음 */
#define GET_ALLOC(p) (GET(p) & 0x1)  /* 0x1은 이진수로 ...00000001 => &연산 시 마지막 할당 비트 하나만 남고 모두 0이 되어 할당 여부를 알 수 있음 */

/* 
 * 블록 포인터(bp)를 가지고 해당 블록의 헤더 주소와 풋터 주소를 계산해주는 매크로
 |   header   |   payload   |   footer   |
   <- 1워드 -> ^(bp)           <- 1워드 ->
 * bp: 페이로드의 시작 주소, 
 * HDRP: bp에서 워드 크기만큼 앞으로 가면 헤더의 시작 주소가 나옴
 * FTRP: bp에서 블록 전체 크기만큼 뒤로 간 다음(다음 블록의 bp), 헤더/푸터 크기(더블 워드)만큼 다시 앞으로 가면 푸터의 시작 주소가 나옴 
 */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 현재 블록 포인터(bp)를 기준으로 다음 블록 또는 이전 블록의 bp 계산 
 * NEXT_BLKP: 현재 블록의 bp에서 현재 블록의 전체 크기(GET_SIZE(...))만큼 뒤로 가면 다음 블록의 페이로드 시작점(bp)이 나옴
 * PREV_BLKP: 현재 bp에서 더블 워드만큼 앞으로 가면 이전 블록의 풋터가 나오고((char *)(bp) - DSIZE),
 * 거기서 이전 블록의 전체 크기를 읽어서(GET_SIZE(...)) 현재 bp에서 그만큼 빼주면 이전 블록의 bp가 나옴 
 */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* static 선언 */
static void *heap_listp; // 힙을 처음부터 끝까지 훑어봐야 할 때 
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 초기 힙 공간 확보: 실제 데이터를 담기 위한 공간이 아닌 힙의 경계선을 표시할 프롤로그/에필로그 블록을 설치하는 데 사용 */
    /* heap_listp: 힙의 시작점 역할을 하는 전역 포인터
     * => 힙을 처음부터 끝까지 훑어봐야 할 때(순회), 그 시작점을 제공해줌
     * 4워드 크기만큼 힙에 공간을 달라고 요청 후(mem_sbrk(4*WSIZE)) 반환받은 해당 공간의 시작 주소값을 heap_listp에 저장해둠 
     */
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1; // 만약 더 이상 줄 공간이 없다면(즉, 메모리가 부족하다면) 요청 살패 리턴
    /* 힙의 뼈대 설정: 힙의 시작과 끝을 표시하고 경계 조건을 쉽게 처리하기 위한 가상 블록들 */
    PUT(heap_listp, 0);                             /* 정렬 패딩: 첫 블록의 페이로드가 8바이트 경계에 정렬되도록 만드는 빈 공간(이게 없으면 첫 블록 페이로드의 시작 주소가 8의 배수가 아니게 됨!!) */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 헤더: 힙의 시작을 알리는 가짜 블록. 연결 작업 시의 경계 역할 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 푸터: 프롤로그 블록의 끝을 표시 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* 에필로그 헤더: 힙의 끝을 알리는 가짜 블록. 탐색 작업 시의 경계 역할 */

    /* 전역 포인터를 패딩과 프롤로그 헤더를 건너뛰어 힙 순회의 시작점이 될 프롤로그 블록의 가상 bp 위치로 이동
     * 해당 위치는 1. 프롤로그 블록의 페이로드 위치이자 2. 프롤로그 블록의 푸터 시작점이다. */
    heap_listp += (2*WSIZE);

    /* 힙을 CHUNKSIZE만큼 확장하여 초기 가용 블록을 생성한다.
     * 이 공간이 있어야 비로소 첫 malloc 요청을 처리할 수 있게 된다. */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * 요청받은 만큼 메모리를 추가로 확보한다.
 * 새로 얻은 공간을 하나의 커다란 '가용 블록(free block)'으로 만든다.
 * 새 블록 바로 앞 블록이 가용 상태였다면, 두 블록을 합쳐서 더 큰 가용 블록으로 만든다.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 더블 워드 정렬(8바이트)을 유지하면서 바이트 크기로 변환 (요청받은 워드의 개수가 홀수이면 1을 더한 뒤 변환) */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 새로 확장된 힙 공간을 가용 블록으로 초기화하고, 새 에필로그 헤더를 설정 */
    PUT(HDRP(bp), PACK(size, 0));                   /* 새 가용 블록의 헤더를 설정("이 블록의 크기는 size이며 가용 상태이다") */
    PUT(FTRP(bp), PACK(size, 0));                   /* 새 가용 블록의 푸터를 설정(헤더와 마찬가지) */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));           /* 힙의 새로운 끝을 표시하는 새 에필로그 헤더를 설정 */

    /* 만약 이전 블록이 가용 상태였다면 새로 만든 블록과 합치기 위해 coalesce 함수 호출 */
    return coalesce(bp);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}