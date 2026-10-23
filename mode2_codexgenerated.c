/* =====================================================================
 *  8-1 Recover the Design   ——  MRV启发式 + 全向搜索版
 *  编译：gcc -O2 -std=c99 -o solver this_file.c
 * ===================================================================== */

#include <stdio.h>
#include <string.h>

#define MAXD 52
#define MAXV 2600

enum { UP, DOWN, LEFT, RIGHT, DIRS };
static const int opposite[DIRS] = { DOWN, UP, RIGHT, LEFT };
static int n, m, cnt;
static int g[MAXD][MAXD], id[MAXD][MAXD];
static int vr[MAXV], vc[MAXV], vk[MAXV];

/* =====================================================================
 * =====================================================================
 *                      ⚠️ 差异区域 1：数据结构大换血 ⚠️
 * ---------------------------------------------------------------------
 * 🔴 原版 prog.c：
 *    - 只有 nxtR, nxtD（只能向右下走）
 *    - 使用 vTop, vBot 扫描线检查交叉（强依赖从左上到右下的固定顺序）
 *
 * 🟢 新版：
 *    - neighbor[MAXV][4] 全向预建图
 *    - horizontal / vertical 二维数组全局标记，不依赖搜索顺序
 * =====================================================================
 * ===================================================================== */
static int neighbor[MAXV][DIRS]; /* 显式保存四个方向的邻居 */
static int deg[MAXV];            /* 已选边贡献的度数，来自任意方向 */
static int chosen[MAXV][DIRS];   /* 答案，顺序为上、下、左、右 */
static int horizontal[MAXD][MAXD], vertical[MAXD][MAXD];
/* =====================================================================
 *                      ⚠️ 差异区域 1 结束 ⚠️
 * ===================================================================== */

#ifdef STAT
static long long nodes, fails;
#endif

/* 只标记边内部经过的格点，不标记连接件端点 */
static int crosses(int i, int j)
{
    int x;
    if (vr[i] == vr[j]) {
        int lo = vc[i] < vc[j] ? vc[i] : vc[j];
        int hi = vc[i] > vc[j] ? vc[i] : vc[j];
        for (x = lo + 1; x < hi; ++x)
            if (vertical[vr[i]][x]) return 1;
    } else {
        int lo = vr[i] < vr[j] ? vr[i] : vr[j];
        int hi = vr[i] > vr[j] ? vr[i] : vr[j];
        for (x = lo + 1; x < hi; ++x)
            if (horizontal[x][vc[i]]) return 1;
    }
    return 0;
}

/* 统一落子/撤销 */
static void change_edge(int i, int d, int delta)
{
    int j = neighbor[i][d], x;
    deg[i] += delta;
    deg[j] += delta;
    chosen[i][d] = chosen[j][opposite[d]] = (delta > 0);
    if (vr[i] == vr[j]) {
        int lo = vc[i] < vc[j] ? vc[i] : vc[j];
        int hi = vc[i] > vc[j] ? vc[i] : vc[j];
        for (x = lo + 1; x < hi; ++x) horizontal[vr[i]][x] += delta;
    } else {
        int lo = vr[i] < vr[j] ? vr[i] : vr[j];
        int hi = vr[i] > vr[j] ? vr[i] : vr[j];
        for (x = lo + 1; x < hi; ++x) vertical[x][vc[i]] += delta;
    }
}

/* =====================================================================
 * =====================================================================
 *                      ⚠️ 差异区域 2：可用方向统计 ⚠️
 * ---------------------------------------------------------------------
 * 🔴 原版 prog.c：
 *    - 方向数被写死：canD + canR（只看右下）
 *    - 并且没有交叉检查的预处理
 *
 * 🟢 新版：
 *    - 扫描上、下、左、右 4 个方向
 *    - 必须确保目标点未满、边未选、且没有与其他线交叉
 * =====================================================================
 * ===================================================================== */
static int available_mask(int i)
{
    int d, mask = 0;
    for (d = 0; d < DIRS; ++d) {
        int j = neighbor[i][d];
        if (j >= 0 && !chosen[i][d] && deg[j] < vk[j] && !crosses(i, j))
            mask |= 1 << d;
    }
    return mask;
}

static int bit_count(int mask)
{
    int count = 0;
    while (mask) {
        count += mask & 1;
        mask >>= 1;
    }
    return count;
}
/* =====================================================================
 *                      ⚠️ 差异区域 2 结束 ⚠️
 * ===================================================================== */


/* =====================================================================
 * =====================================================================
 *                      ⚠️ 差异区域 3：DFS 核心架构 ⚠️
 * ---------------------------------------------------------------------
 * 🔴 原版 prog.c：
 *    - static int dfs(int i)
 *    - 参数 i 固定推进，按照行优先顺序处理每个点
 *    - 剪枝是局部的 accept(i, j)
 *
 * 🟢 新版：
 *    - static int dfs(int depth)
 *    - 每次进入 dfs，全局扫描，找出最危险的点（三层漏斗）
 *    - 尝试的方向不是固定的下/右，而是枚举四个方向
 * =====================================================================
 * ===================================================================== */
static int dfs(int depth)
{
    int i, best = -1, best_avail = DIRS + 1, best_need = -1;
    int best_mask = 0, d;
    (void)depth;
#ifdef STAT
    ++nodes;
#endif
    
    /* 全局扫描，寻找“最危险”的节点 */
    for (i = 0; i < cnt; ++i) {
        int need = vk[i] - deg[i], candidate, avail;
        if (need < 0) goto fail;
        
        candidate = available_mask(i);
        avail = bit_count(candidate);
        
        /* 第一关（看死活）：可连方向 < 剩余度数，直接宣告死刑 */
        if (avail < need) goto fail; 
        
        if (need == 0) continue;     /* 已满的点无需再连边 */
        
        /* 第二关（找绝路） + 第三关（平局裁定） */
        if (avail < best_avail || 
            (avail == best_avail && need > best_need)) {
            best = i;
            best_avail = avail;
            best_need = need;
            best_mask = candidate;
        }
    }
    
    /* 如果找不到需要处理的节点，说明全盘通关 */
    if (best < 0) return 1;
    
    /* 遍历选出的最优节点的全部可连方向 */
    for (d = 0; d < DIRS; ++d) {
        if (!(best_mask & (1 << d))) continue;
        
        change_edge(best, d, 1);  /* 落子 */
        if (dfs(depth + 1)) return 1; /* 递归 */
        change_edge(best, d, -1); /* 回溯 */
    }
    
fail:
#ifdef STAT
    ++fails;
#endif
    return 0;
}
/* =====================================================================
 *                      ⚠️ 差异区域 3 结束 ⚠️
 * ===================================================================== */


int main(void)
{
    int r, c, i, last, sum = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > 50 || m < 1 || m > 50) return 0;
    for (r = 0; r < n; ++r)
        for (c = 0; c < m; ++c) {
            if (scanf("%d", &g[r][c]) != 1) return 0;
            if (g[r][c] < 0 || g[r][c] > 4) return 0;
            sum += g[r][c];
        }

    memset(neighbor, -1, sizeof(neighbor));
    for (r = 0; r < n; ++r)
        for (c = 0; c < m; ++c) {
            id[r][c] = -1;
            if (g[r][c]) {
                id[r][c] = cnt;
                vr[cnt] = r;
                vc[cnt] = c;
                vk[cnt++] = g[r][c];
            }
        }
        
    /* =====================================================================
     * =====================================================================
     *                      ⚠️ 差异区域 4：建图方式 ⚠️
     * ---------------------------------------------------------------------
     * 🔴 原版 prog.c：
     *    - 只建了 nxtR（向右的邻居）和 nxtD（向下的邻居）
     *
     * 🟢 新版：
     *    - 由于搜索是全向的，必须把上、下、左、右的邻居全建出来
     *    - 这里使用 neighbor[last][RIGHT] 和 neighbor[i][LEFT] 双向建图
     * =====================================================================
     * ===================================================================== */
    for (r = 0; r < n; ++r) {
        last = -1;
        for (c = 0; c < m; ++c) {
            i = id[r][c];
            if (i < 0) continue;
            if (last >= 0) {
                neighbor[last][RIGHT] = i;
                neighbor[i][LEFT] = last;
            }
            last = i;
        }
    }
    for (c = 0; c < m; ++c) {
        last = -1;
        for (r = 0; r < n; ++r) {
            i = id[r][c];
            if (i < 0) continue;
            if (last >= 0) {
                neighbor[last][DOWN] = i;
                neighbor[i][UP] = last;
            }
            last = i;
        }
    }
    /* =====================================================================
     *                      ⚠️ 差异区域 4 结束 ⚠️
     * ===================================================================== */

    if ((sum & 1) || !dfs(0)) {
        printf("No Solution\n");
    } else {
        for (i = 0; i < cnt; ++i)
            printf("%d %d %d %d %d %d\n", vr[i] + 1, vc[i] + 1,
                   chosen[i][UP], chosen[i][DOWN],
                   chosen[i][LEFT], chosen[i][RIGHT]);
    }
    
#ifdef STAT
    fprintf(stderr, "nodes=%lld fails=%lld\n", nodes, fails);
#endif
    return 0;
}
