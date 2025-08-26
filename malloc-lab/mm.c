/*
 * -----------------------------------------------------------------------------
 * [설계 개요 — explicit free list 버전 (64-bit 기준)]
 * - 블록 포맷(64-bit 기준):
 * [header: 8B | payload ... | footer: 8B]
 * * header/footer의 하위 3비트는 alloc/prev-alloc 등 비트로 사용(여기선 alloc 1비트)
 * * header/footer의 나머지 비트는 블록 전체 크기(헤더~푸터 포함)
 * - 정렬: 16바이트(DSIZE) 정렬 유지
 * - "가용 블록"의 payload 앞부분을 이용하여 가용리스트 더블 링크 포인터를 저장:
 * free block payload 레이아웃: [pred ptr: 8B | succ ptr: 8B | ... (나머지 payload) ...]
 * 즉, explicit free list를 위해 pred/succ 포인터를 payload에 박아둠.
 * - 전역 포인터 free_list_head: 가장 앞의 가용 블록을 가리키는 LIFO 단일 진입점
 * - 핵심 불변식:
 * 1) 가용 블록만 free list에 존재(할당 블록은 리스트에 절대 포함 X)
 * 2) 리스트의 pred/succ 포인터는 양방향으로 일관성 유지
 * (prev->succ == me, next->pred == me)
 * 3) coalesce 시 결합되는 이웃 free 블록은 리스트에서 제거 후,
 * 합쳐진 새 free 블록을 리스트에 다시 삽입
 * - 탐색(find_fit): explicit free list를 선형 스캔(first-fit)
 * - 배치(place): 필요 시 앞쪽을 할당, 뒤쪽 잔여를 새 free 블록으로 분할하여 리스트에 재삽입
 * - 확장(extend_heap): 새로 생긴 큰 free 블록을 coalesce 한 뒤 free list에 삽입
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
#define WSIZE sizeof(void *)
#define DSIZE (2 * WSIZE)
#define CHUNKSIZE  (1<<12)   /* 힙 공간이 부족할 때, sbrk를 통해 추가로 요청할 메모리의 기본 크기 (4096바이트) */

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* 헤더와 푸터 관리 유틸: 크기+할당비트를 한 워드로 PACK/GET/PUT */
#define PACK(size, alloc) ((size) | (alloc))

/* 64비트 환경이므로 size_t (보통 unsigned long)를 사용하여 8바이트 단위로 읽고 씀 */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* 헤더/푸터의 크기/할당비트 추출 */
#define GET_SIZE(p)  (GET(p) & ~0x7) /* 하위 3비트를 0으로 만들어 순수 사이즈만 추출 */
#define GET_ALLOC(p) (GET(p) & 0x1)  /* 최하위 비트로 할당 여부 확인 */
/*
 * 블록 포인터(bp)를 가지고 헤더/푸터 주소 계산
 * bp는 항상 "payload의 시작"을 가리킨다.
 */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                         /* payload 앞의 header */
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)    /* 블록 끝의 footer */

/* 인접 블록의 bp 계산
 * NEXT_BLKP: 현재 블록의 총 크기만큼 전진 → 다음 블록의 payload 시작
 * PREV_BLKP: 현재 bp 바로 앞(=이전 블록 footer 위치)에서 size를 읽어 그만큼 후퇴 → 이전 블록 payload 시작
 */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* explicit free list 전용: 가용 블록 payload 앞부분을 pred/succ 포인터 저장용으로 사용 */
#define PTRSIZE        (sizeof(void*))    /* 포인터 크기는 64비트에서 8바이트 */
#define PRED_P(bp)     (*(void **)(bp))                                   /* [bp + 0]: 이전 free 블록 포인터 */
#define SUCC_P(bp)     (*(void **)((char *)(bp) + PTRSIZE))               /* [bp + PTRSIZE]: 다음 free 블록 포인터 */

#define SET_PRED(bp, p) (PRED_P(bp) = (p))
#define SET_SUCC(bp, p) (SUCC_P(bp) = (p))

/* 가용 블록으로 분할이 가능하려면 최소한
 * Header(WSIZE) + Footer(WSIZE) + Pred_Pointer(PTRSIZE) + Succ_Pointer(PTRSIZE)
 * 이 필요하다. (= 2*WSIZE + 2*PTRSIZE)
 * 이보다 작은 잔여 공간은 쪼개지지 않고 통째로 할당해버리는 게 맞음. */
#define MIN_FREE_BLK   (2*WSIZE + 2*PTRSIZE)   // 64bit 기준: 2*8 + 2*8 = 32

/* static 전역 포인터들 */
static void *heap_listp;              /* Implicit 순회를 위한 포인터 */
static void *free_list_head = NULL;   /* EXPLICIT: 가용 리스트의 시작점을 가리키는 포인터 (LIFO) */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
/*
 * [explicit helper] 가용 리스트의 맨 앞에 새 블록을 삽입 (LIFO).
 * - 새 블록(bp)이 새로운 head가 된다.
 * - bp의 다음은 기존 head, 이전은 NULL로 설정.
 * - 기존 head가 있었다면, 그것의 이전을 bp로 연결.
 */
static void insert_to_free_list(void *bp) {
    void *old_head = free_list_head;
    SET_PRED(bp, NULL);
    SET_SUCC(bp, old_head);
    if (old_head) {
        SET_PRED(old_head, bp);
    }
    free_list_head = bp;
}

/* 
[explicit helper] 가용 리스트에서 제거.
*/
static void remove_from_free_list(void *bp) {
    void *prev = PRED_P(bp);
    void *next = SUCC_P(bp);

    // 1. 이전 노드(prev)의 다음(succ)을 나의 다음(next)으로 연결
    if (prev) {
        SET_SUCC(prev, next);
    } 
    // 만약 이전 노드가 없다면, 내가 head였다는 의미이므로
    // 리스트의 head를 나의 다음(next)으로 변경
    else { 
        free_list_head = next;
    }

    // 2. 다음 노드(next)의 이전(pred)을 나의 이전(prev)으로 연결
    if (next) {
        SET_PRED(next, prev);
    }
}

/*
 * mm_init - 힙과 가용 리스트를 초기화
 */
int mm_init(void)
{
    free_list_head = NULL;

    /* 힙의 뼈대(프롤로그/에필로그) 확보 */
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_listp, 0);                             /* 정렬 패딩 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 헤더(가짜 블록, size=16, alloc=1) */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 푸터 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* 에필로그 헤더(size=0, alloc=1) */

    heap_listp += (2*WSIZE);                        /* 프롤로그의 가상 bp로 이동 */

    /* 초기 힙을 CHUNKSIZE만큼 확장 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }

    return 0;
}

/*
 * extend_heap: 힙을 확장하고, 새로 생긴 가용 블록을 리스트에 추가
 */
static void *extend_heap(size_t words)
{
    char *bp;
    
    /* 16바이트 정렬 유지: 홀수 words라면 +1하여 짝수로 맞춘 뒤 바이트 환산 */
    size_t size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* [free block | epilogue] 구성 */
    PUT(HDRP(bp), PACK(size, 0));                   /* 새 free 블록 header */
    PUT(FTRP(bp), PACK(size, 0));                   /* 새 free 블록 footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));           /* 새 에필로그 header */

    /* 인접 블록 상황 따라 병합 */
    return coalesce(bp);
}

/*
 * mm_malloc - 요청 크기를 정렬/오버헤드 반영해 asize로 조정
 */
void *mm_malloc(size_t size)
{
    size_t asize;           /* 실제 할당할 조정된 블록 크기 */
    size_t extendsize;      /* 공간이 없을 때 힙을 확장할 크기 */
    char *bp;

    if (size == 0)
        return NULL;

    /* 요청 크기 → 더블워드 정렬/오버헤드 포함 크기로 반올림 */
    if (size <= 2*PTRSIZE) {  /* 요청 크기가 Pred, Succ 두 포인터 크기의 합보다 작다면 그냥 최소 가용 블록 크기 만큼 요청 */
        asize = MIN_FREE_BLK;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    /* 가용 리스트에서 first-fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 적합 블록이 없으면 힙 확장 후 할당 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free: 블록을 해제하고, coalesce를 통해 가용 리스트에 다시 추가
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    /* EXPLICIT: coalesce가 이제 병합과 동시에 가용 리스트 추가까지 담당함 */
    coalesce(ptr);
}

/*
 * coalesce: 주변 블록과 병합하고, 최종 가용 블록을 리스트에 추가
 */
static void *coalesce(void *bp)
{
    void *prev_bp = PREV_BLKP(bp);
    void *next_bp = NEXT_BLKP(bp);
    
    size_t prev_alloc = GET_ALLOC(HDRP(prev_bp));
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t size = GET_SIZE(HDRP(bp));

    /* 이웃이 free면 먼저 리스트에서 제거 */
    if (!prev_alloc) {
        remove_from_free_list(prev_bp);
    }
    if (!next_alloc) {
        remove_from_free_list(next_bp);
    }

    /* 병합 로직 */
    if (!prev_alloc && !next_alloc) { /* Case 4: 양쪽 모두 free */
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp));
        bp = prev_bp;
    } else if (!prev_alloc && next_alloc) { /* Case 2: 왼쪽만 free */
        size += GET_SIZE(HDRP(prev_bp));
        bp = prev_bp;
    } else if (prev_alloc && !next_alloc) { /* Case 3: 오른쪽만 free */
        size += GET_SIZE(HDRP(next_bp));
    }
    /* Case 1 (양쪽 모두 allocated)는 아무것도 하지 않음 */

    /* 새 크기로 헤더/푸터 업데이트 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    /* 병합 결과 블록을 free list 머리에 삽입(LIFO) */
    insert_to_free_list(bp);
    return bp;
}

/*
 * find_fit: 가용 리스트(free_list)만 탐색하여 적절한 블록을 찾음 (First-Fit)
 */
static void *find_fit(size_t asize) {
    /* EXPLICIT: 힙 전체가 아닌, free_list_head부터 SUCC_P 포인터를 따라 가용 블록만 순회 */
    for (void *bp = free_list_head; bp != NULL; bp = SUCC_P(bp)) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }
    }
    return NULL;
}

/*
 * place: 찾은 가용 블록에 요청한 크기만큼 할당하고, 남는 부분은 분할
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    /* EXPLICIT: 할당하기 직전에, 해당 블록을 가용 리스트에서 제거 */
    remove_from_free_list(bp);

    size_t rem = csize - asize;

    // 남는 공간이 최소 가용 블록 크기보다 크면 분할
    if (rem >= MIN_FREE_BLK) {
        /* 앞쪽 asize를 할당 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        /* 뒤쪽 잔여를 새 free 블록으로 세팅하고 리스트에 넣음 */
        void *rbp = NEXT_BLKP(bp);
        PUT(HDRP(rbp), PACK(rem, 0));
        PUT(FTRP(rbp), PACK(rem, 0));

        /* EXPLICIT: 분할하고 남은 새 가용 블록을 리스트에 다시 추가 */
        insert_to_free_list(rbp);
    } else {
        /* 잔여가 너무 작으면 통째로 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_realloc
 * - 축소/확장 시 가능한 경우 블록을 재사용
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

    size_t old_csize = GET_SIZE(HDRP(bp));
    size_t new_asize;

    // 새로 필요한 블록 크기 계산 (더블워드 정렬)
    if (size <= DSIZE) {
        new_asize = 2 * DSIZE;
    } else {
        new_asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }
    
    if (new_asize < MIN_FREE_BLK) {
        new_asize = MIN_FREE_BLK;
    }


    /* [축소] 요청 크기가 더 작거나 같을 경우 */
    if (new_asize <= old_csize) {
        size_t rem = old_csize - new_asize;
        // 남는 공간이 최소 가용 블록 크기 이상이면 분할
        if (rem >= MIN_FREE_BLK) {
            PUT(HDRP(bp), PACK(new_asize, 1));
            PUT(FTRP(bp), PACK(new_asize, 1));
            void *rbp = NEXT_BLKP(bp);
            PUT(HDRP(rbp), PACK(rem, 0));
            PUT(FTRP(rbp), PACK(rem, 0));
            coalesce(rbp);
        }
        // 남는 공간이 작으면 분할하지 않고 그대로 사용
        return bp;
    }

    /* [확장] 요청 크기가 더 클 경우 */
    void *next_bp = NEXT_BLKP(bp);
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t next_size = GET_SIZE(HDRP(next_bp));
    size_t total_size = old_csize + next_size;

    // 바로 뒷 블록이 가용 블록이고, 합친 크기가 충분한 경우
    if (!next_alloc && total_size >= new_asize) {
        remove_from_free_list(next_bp); // 합치기 전에 뒤 블록을 free list에서 제거
        
        size_t rem = total_size - new_asize;
        if (rem >= MIN_FREE_BLK) {
            // 합친 후 분할
            PUT(HDRP(bp), PACK(new_asize, 1));
            PUT(FTRP(bp), PACK(new_asize, 1));
            void *rbp = NEXT_BLKP(bp);
            PUT(HDRP(rbp), PACK(rem, 0));
            PUT(FTRP(rbp), PACK(rem, 0));
            insert_to_free_list(rbp);
        } else {
            // 합친 후 통째로 사용
            PUT(HDRP(bp), PACK(total_size, 1));
            PUT(FTRP(bp), PACK(total_size, 1));
        }
        return bp;
    }

    /* [최후의 수단] 새로 할당 후 복사 */
    void *new_bp = mm_malloc(size);
    if (new_bp == NULL) {
        return NULL;
    }
    size_t copySize = GET_SIZE(HDRP(bp)) - DSIZE; // payload 크기
    if (size < copySize) {
        copySize = size;
    }
    memcpy(new_bp, bp, copySize);
    mm_free(bp);
    return new_bp;
}