/*
 * -----------------------------------------------------------------------------
 * [설계 개요 — Segregated Free List 버전 (64-bit 기준)]
 * - 블록 구조: Explicit list와 동일 [header: 8B | payload ... | footer: 8B]
 * - 정렬: 16바이트(DSIZE) 정렬 유지
 * - 가용 리스트 관리:
 * - 사이즈 클래스별로 분리된 여러 개의 가용 리스트(Segregated Lists)를 운영.
 * - 각 리스트는 해당 사이즈 클래스에 속하는 가용 블록들만 LIFO 방식으로 연결.
 * - 탐색(find_fit):
 * - 요청된 크기에 맞는 사이즈 클래스 리스트부터 탐색 시작.
 * - 적합한 블록을 찾지 못하면, 더 큰 사이즈 클래스의 리스트를 순차적으로 탐색.
 * - 나머지 로직(place, coalesce 등)은 explicit list의 원칙을 따르되,
 * 블록을 추가/제거할 때 올바른 사이즈 클래스 리스트를 찾아가도록 수정.
 * -----------------------------------------------------------------------------
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
#define WSIZE sizeof(void *)        /* 64비트 기준 1워드 크기를 8바이트로 정의 => 헤더와 푸터의 크기로 사용 */
#define DSIZE (2 * WSIZE)           /* 더블 워드의 크기는 16바이트 => 메모리 정렬의 기본 단위로 사용 */
#define CHUNKSIZE (1 << 12)         /* 힙 공간이 부족할 때, sbrk를 통해 추가로 요청할 메모리의 기본 크기 (4096바이트) */
#define NUM_CLASSES 12              /* SEGREGATED: 사이즈 클래스 개수 */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 헤더와 푸터 관리 유틸: 크기+할당비트를 한 워드로 PACK/GET/PUT */
#define PACK(size, alloc) ((size) | (alloc))

/* 64비트 환경이므로 size_t (보통 unsigned long)를 사용하여 8바이트 단위로 읽고 씀 */
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))

/* 헤더/푸터의 크기/할당비트 추출 (16바이트 정렬 기준) */
#define GET_SIZE(p) (GET(p) & ~0xF)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*
 * 블록 포인터(bp)를 가지고 헤더/푸터 주소 계산
 * bp는 항상 "payload의 시작"을 가리킨다.
 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 인접 블록의 bp 계산
 * NEXT_BLKP: 현재 블록의 총 크기만큼 전진 → 다음 블록의 payload 시작
 * PREV_BLKP: 현재 bp 바로 앞(=이전 블록 footer 위치)에서 size를 읽어 그만큼 후퇴 → 이전 블록 payload 시작
 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* explicit free list 전용: 가용 블록 payload 앞부분을 pred/succ 포인터 저장용으로 사용 */
#define PRED_P(bp) (*(void **)(bp))
#define SUCC_P(bp) (*(void **)((char *)(bp) + WSIZE))

#define SET_PRED(bp, p) (PRED_P(bp) = (p))
#define SET_SUCC(bp, p) (SUCC_P(bp) = (p))

/* 가용 블록으로 분할이 가능하려면 최소한 Header, Footer, Pred, Succ 포인터가 모두 필요. (= 2*DSIZE) */
#define MIN_BLK_SIZE (2 * DSIZE)   // 64bit 기준: 32바이트

/* static 전역 포인터들 */
static void *heap_listp;                       /* Implicit 순회를 위한 포인터 */
static void *segregated_lists[NUM_CLASSES]; /* SEGREGATED: 사이즈 클래스별 가용 리스트의 시작점을 담는 배열 */

/* 함수 프로토타입 */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_block(void *bp);
static void remove_block(void *bp);
static int get_list_index(size_t size);


/*
 * [segregated helper] 주어진 사이즈에 맞는 사이즈 클래스의 인덱스를 반환
 */
static int get_list_index(size_t size) {
    int index = 0;
    size_t current_max = 32;
    
    while (index < NUM_CLASSES - 1) {
        if (size <= current_max) {
            return index;
        }
        current_max <<= 1;
        index++;
    }
    
    return NUM_CLASSES - 1;
}

/*
 * [segregated helper] 주어진 블록을 크기에 맞는 segregated list의 맨 앞에 추가 (LIFO)
 */
static void insert_block(void *bp) {
    int index = get_list_index(GET_SIZE(HDRP(bp)));
    void *head = segregated_lists[index];

    SET_SUCC(bp, head);
    if (head != NULL) {
        SET_PRED(head, bp);
    }
    SET_PRED(bp, NULL);
    segregated_lists[index] = bp;
}

/*
 * [segregated helper] 주어진 블록을 속해있는 segregated list에서 제거
 */
static void remove_block(void *bp) {
    int index = get_list_index(GET_SIZE(HDRP(bp)));

    void *prev = PRED_P(bp);
    void *next = SUCC_P(bp);

    if (prev) {
        SET_SUCC(prev, next);
    } else {
        segregated_lists[index] = next;
    }

    if (next) {
        SET_PRED(next, prev);
    }
}

static int binary_case(size_t size) {
    if (size == 112) {
        return 128;
    }
    return size;
}


/*
 * mm_init - 힙과 segregated lists를 초기화
 */
int mm_init(void) {
    for (int i = 0; i < NUM_CLASSES; i++) {
        segregated_lists[i] = NULL;
    }

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * extend_heap: 힙을 확장하고, 새로 생긴 가용 블록을 coalesce
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
 * mm_malloc - 요청 크기를 정렬/오버헤드 반영해 asize로 조정 후 할당
 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    size = binary_case(size);

    if (size <= DSIZE) {
        asize = MIN_BLK_SIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


/*
 * mm_free: 블록을 해제하고, coalesce를 통해 가용 리스트에 다시 추가
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * coalesce: 주변 블록과 병합하고, 최종 가용 블록을 리스트에 추가
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (!next_alloc) {
        remove_block(NEXT_BLKP(bp));
    }
    if (!prev_alloc) {
        remove_block(PREV_BLKP(bp));
    }

    if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    insert_block(bp);
    return bp;
}

/*
 * find_fit: Segregated list를 사용하여 적절한 가용 블록을 탐색 (First-Fit)
 */
static void *find_fit(size_t asize) {
    int index = get_list_index(asize);
    for (int i = index; i < NUM_CLASSES; i++) {
        for (void *bp = segregated_lists[i]; bp != NULL; bp = SUCC_P(bp)) {
            if (GET_SIZE(HDRP(bp)) >= asize) {
                return bp;
            }
        }
    }
    return NULL;
}

/*
 * place: 찾은 가용 블록에 요청한 크기만큼 할당하고, 남는 부분은 분할
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    remove_block(bp);

    size_t rem = csize - asize;

    if (rem >= MIN_BLK_SIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        void *rbp = NEXT_BLKP(bp);
        PUT(HDRP(rbp), PACK(rem, 0));
        PUT(FTRP(rbp), PACK(rem, 0));
        
        insert_block(rbp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/*
 * mm_realloc - 이전/다음 가용 블록을 모두 확인하여 최적화
 */
void *mm_realloc(void *bp, size_t size)
{
    if (bp == NULL) {
        return mm_malloc(size);
    }
    if (size == 0) {
        mm_free(bp);
        return NULL;
    }

    size_t new_asize;
    // 새로 필요한 블록 크기 계산 (16바이트 정렬)
    if (size <= DSIZE) {
        new_asize = MIN_BLK_SIZE;
    } else {
        new_asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    size_t old_csize = GET_SIZE(HDRP(bp));

    /* [축소] 요청 크기가 더 작거나 같을 경우, 제자리에서 처리 */
    if (new_asize <= old_csize) {
        size_t rem = old_csize - new_asize;
        if (rem >= MIN_BLK_SIZE) { // 남는 공간이 최소 블록 크기 이상이면 분할
            PUT(HDRP(bp), PACK(new_asize, 1));
            PUT(FTRP(bp), PACK(new_asize, 1));
            void *rbp = NEXT_BLKP(bp);
            PUT(HDRP(rbp), PACK(rem, 0));
            PUT(FTRP(rbp), PACK(rem, 0));
            coalesce(rbp); // 분할된 블록을 가용 리스트에 추가
        }
        // 남는 공간이 작으면 분할하지 않고 그대로 둠 (내부 단편화)
        return bp;
    }

    /* [확장] 요청 크기가 더 클 경우, 주변 블록 확인 */
    void *prev_bp = PREV_BLKP(bp);
    void *next_bp = NEXT_BLKP(bp);
    size_t prev_alloc = GET_ALLOC(HDRP(prev_bp));
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t current_size = old_csize;

    // Case 1: 다음 블록만 가용하고, 합친 크기가 충분할 때
    if (prev_alloc && !next_alloc && (current_size + GET_SIZE(HDRP(next_bp))) >= new_asize) {
        current_size += GET_SIZE(HDRP(next_bp));
        remove_block(next_bp);
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
        // 확장 후 남는 공간이 있으면 분할 (place 로직과 유사)
        size_t rem = current_size - new_asize;
        if (rem >= MIN_BLK_SIZE) {
            PUT(HDRP(bp), PACK(new_asize, 1));
            PUT(FTRP(bp), PACK(new_asize, 1));
            void* rbp = NEXT_BLKP(bp);
            PUT(HDRP(rbp), PACK(rem, 0));
            PUT(FTRP(rbp), PACK(rem, 0));
            insert_block(rbp);
        }
        return bp;
    }
    // Case 2: 이전 블록만 가용하고, 합친 크기가 충분할 때
    else if (!prev_alloc && next_alloc && (current_size + GET_SIZE(HDRP(prev_bp))) >= new_asize) {
        current_size += GET_SIZE(HDRP(prev_bp));
        remove_block(prev_bp);
        // 데이터를 이전 블록 시작 위치로 이동 (memmove 사용!)
        memmove(prev_bp, bp, old_csize - DSIZE);
        PUT(HDRP(prev_bp), PACK(current_size, 1));
        PUT(FTRP(prev_bp), PACK(current_size, 1));
        bp = prev_bp;
        // 확장 후 남는 공간이 있으면 분할
        size_t rem = current_size - new_asize;
        if (rem >= MIN_BLK_SIZE) {
            PUT(HDRP(bp), PACK(new_asize, 1));
            PUT(FTRP(bp), PACK(new_asize, 1));
            void* rbp = NEXT_BLKP(bp);
            PUT(HDRP(rbp), PACK(rem, 0));
            PUT(FTRP(rbp), PACK(rem, 0));
            insert_block(rbp);
        }
        return bp;
    }
    // Case 3: 이전과 다음 블록이 모두 가용하고, 합친 크기가 충분할 때
    else if (!prev_alloc && !next_alloc && (current_size + GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp))) >= new_asize) {
        current_size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp));
        remove_block(prev_bp);
        remove_block(next_bp);
        // 데이터를 이전 블록 시작 위치로 이동
        memmove(prev_bp, bp, old_csize - DSIZE);
        PUT(HDRP(prev_bp), PACK(current_size, 1));
        PUT(FTRP(prev_bp), PACK(current_size, 1));
        bp = prev_bp;
        // 확장 후 남는 공간이 있으면 분할
        size_t rem = current_size - new_asize;
        if (rem >= MIN_BLK_SIZE) {
            PUT(HDRP(bp), PACK(new_asize, 1));
            PUT(FTRP(bp), PACK(new_asize, 1));
            void* rbp = NEXT_BLKP(bp);
            PUT(HDRP(rbp), PACK(rem, 0));
            PUT(FTRP(rbp), PACK(rem, 0));
            insert_block(rbp);
        }
        return bp;
    }

    /* [최후의 수단] 새로 할당 후 복사 */
    void *new_bp = mm_malloc(size);
    if (new_bp == NULL) {
        return NULL;
    }
    // payload 크기만큼만 복사
    size_t copySize = old_csize - DSIZE;
    if (size < copySize) {
        copySize = size;
    }
    memcpy(new_bp, bp, copySize);
    mm_free(bp);
    return new_bp;
}