/* =====================================================================
 *  8-1  Recover the Design   ——  完整题解（回溯 + 剪枝 + 交叉检查）
 * =====================================================================
 *
 *  【题意】
 *   n × m 的网格，格点上放着一些“连接件”，数字 k (1..4) 表示有几条
 *   栅栏在这个连接件上汇合；0 表示该格点没有连接件。
 *   要还原整张栅栏图。
 *
 *  【三条约束】
 *   1. 栅栏不能弯，只能是水平/竖直的一段直线；
 *   2. 栅栏不能在没有连接件的地方交叉；
 *   3. 栅栏的两端、以及所有拐角，都必须是连接件。
 *
 *  【建模】
 *   由约束 3：一条栅栏从某个连接件出发，中间若经过没有连接件的格点，
 *   只能笔直穿过（不能停、不能拐），所以它一定终止于该方向上“最近的
 *   那个连接件”。于是：
 *
 *       顶点 = 所有连接件
 *       边   = 同一行 / 同一列里“相邻两个连接件”之间的一条栅栏
 *
 *   问题变成：在这个图上选一个子图，使每个顶点的度恰好等于 k。
 *   注意“整条挑或不挑”——栅栏不能只画半截，半截的端点没有连接件。
 *
 *  【搜索】
 *   把连接件按“行优先”（从上到下、从左到右）编号 0..V-1。
 *   任何一条边，两端的编号必是一大一小：往右/往下的边，另一端编号更大。
 *   约定每条边都“归它编号小的那一端决定”，于是处理到 i 时：
 *
 *       i 左边、上边的边全部已经定好  =>  deg[i] 已是终值
 *       i 只需要决定“下”“右”两条边挑不挑  =>  分支因子 <= 2
 *
 *   且必须满足   d + r = k[i] - deg[i]   （d, r ∈ {0,1}）
 *
 *  【剪枝】见 accept()
 *  【交叉】见 crosses 所在的代码段
 *
 *  复杂度：搜索上界 O(m * 2^V)，V 最多 2500。
 *  编译：  gcc -O2 -std=c99 -o prog prog.c
 *  加 -DSTAT 可以在 stderr 看到搜索节点数（写测试报告时有用）。
 * ===================================================================== */

#include <stdio.h>
#include <string.h>
#include <time.h>

/* =====================================================================
 * 修改区域：高精度计时模块
 * 说明：将原有的 clock() 替换为跨平台的高精度计时（Windows / Linux）。
 *       其他所有逻辑保持不变。
 （如果是windows,启用QueryPerformanceFrequency（）；如果是mac/Linux,启用clock_gettime（）。
 比原来的clock()精度更高，因为我们的程序原本的运行时间就很短，所以对精度要求也更高。）
 * ===================================================================== */
#ifdef _WIN32
#include <windows.h>
static double get_time() {
    LARGE_INTEGER freq, counter;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&counter);
    return (double)counter.QuadPart / (double)freq.QuadPart;
}
#else
static double get_time() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
#endif

/* CPU time, excluding input/output; stderr preserves the answer format. */
static double timer_begin, timer_search_begin;
static void report_timing(const char *solver, int searched)
{
    double end = get_time();
    double split = searched ? timer_search_begin : end;
    
    fprintf(stderr,
            "[timing] solver=%s preprocess_ms=%.6f search_ms=%.6f total_ms=%.6f search_started=%d\n",
            solver,
            (split - timer_begin) * 1000.0,
            searched ? (end - split) * 1000.0 : 0.0,
            (end - timer_begin) * 1000.0,
            searched);
}
/* =====================================================================
 * 修改区域结束
 * ===================================================================== */

#define MAXD 52          /* 网格最大 50×50，留点余量 */
#define MAXV 2600        /* 最多 2500 个连接件 */

/* ---------- 输入与编号 ---------- */
static int n, m;                 /* 行数、列数 */
static int g[MAXD][MAXD];        /* 原始输入：格点上的数字 */
static int id[MAXD][MAXD];       /* 格点 -> 连接件编号；-1 表示没有连接件 */
static int cnt;                  /* 连接件个数 V */

/* ---------- 每个连接件的属性 ---------- */
static int vr[MAXV], vc[MAXV];   /* 编号 -> 行、列（0 起） */
static int vk[MAXV];             /* 编号 -> 度数 k */

/* ---------- 候选边：每个连接件只记“右”和“下”两条 ----------
 * 往左、往上的边会由对面的点记下来，这里不重复存。
 * -1 表示那个方向上没有连接件。                                */
static int nxtR[MAXV];           /* 右边最近的连接件 */
static int nxtD[MAXV];           /* 下边最近的连接件 */
static int prevR[MAXV];          /* 左边最近的连接件（判断“左边还用不用得上”）*/

/* ---------- 搜索状态 ---------- */
static int deg[MAXV];            /* 已经确定的度数（来自左、上两边） */
static int eU[MAXV], eD[MAXV], eL[MAXV], eR[MAXV];  /* 答案：四方向有没有栅栏 */

/* ---------- 交叉检查用的扫描线 ----------
 * vTop[c] / vBot[c]：第 c 列当前那条竖直栅栏覆盖的行区间上/下端。
 * 竖直段总是从上往下依次放置，所以每列只需要记“最靠下”的那一段；
 * -1 表示这一列还没有竖直段。                                    */
static int vTop[MAXD], vBot[MAXD];

#ifdef STAT
static long long nodes, fails;   /* 调试用：搜索了多少个 / 剪掉了多少个 */
#endif

/* =====================================================================
 *  accept：从 i 拉一条边到 j 之后，j 还来不来得及把度数凑满？
 * ---------------------------------------------------------------------
 *  两条判据：
 *    (1) 度数不能超：deg[j] + 1 <= k[j]
 *    (2) 剩下的需求 <= j 还能用的边数
 *
 *  第二条里最容易写错的是“j 左边那一条”：
 *    - prevR[j] > i ：j 的左邻居还没被处理，以后还能给 j 送一条  -> 算 1
 *    - prevR[j] == i：左边就是眼下这条边，已经算在 need 里了      -> 不能再算
 *    - prevR[j] < i ：左边早已处理完，定死了                        -> 不算
 *    - prevR[j] < 0 ：左边根本没有连接件                            -> 不算
 *
 *  为什么没有 prevD（上边）？
 *  accept 只在两种时候被调用：j = nxtD[i]（往下）或 j = nxtR[i]（往右）。
 *    - 往下：j 的上邻就是 i 自己，这条边已经在 need 里算过；
 *    - 往右：j 的上邻在更早的行，编号一定 < i，早就定死了。
 *  所以“上边”永远不会是“还没轮到”的状态，不需要 prevD。
 * ===================================================================== */
static int accept(int i, int j)
{
    int need, avail;

    if (deg[j] + 1 > vk[j]) return 0;        /* j 已经满了，接不住 */

    need  = vk[j] - deg[j] - 1;              /* 这条边算上以后，j 还差几条 */
    avail = (nxtR[j] >= 0)                   /* 右边还有连接件            */
          + (nxtD[j] >= 0)                   /* 下边还有连接件            */
          + (prevR[j] > i);                  /* 左边那个点还没被处理      */
    return need <= avail;
}

/* =====================================================================
 *  dfs(i)：处理第 i 个连接件；成功返回 1，失败返回 0
 * ===================================================================== */
static int dfs(int i)
{
    int need;                 /* 还差几条边 */
    int canD, canR;           /* 下、右方向上是否还有连接件 */
    int jd, jr;               /* 下、右方向上那个连接件的编号 */
    int d, r;                 /* 本次决定：d=1 挑“下”，r=1 挑“右” */

    if (i == cnt) return 1;   /* 所有点都处理完：找到解 */

#ifdef STAT
    nodes++;
#endif

    need = vk[i] - deg[i];
    if (need < 0) return 0;   /* 前面替它记多了，矛盾 */

    canD = (nxtD[i] >= 0);
    canR = (nxtR[i] >= 0);
    if (need > canD + canR) return 0;   /* 剩下的边不够凑，必死 */

    jd = canD ? nxtD[i] : -1;
    jr = canR ? nxtR[i] : -1;

    /* 枚举 d = 0,1；r 由等式 r = need - d 唯一决定，且只能是 0/1。 */
    for (d = 0; d <= 1; ++d) {
        int oldTop, oldBot, col;      /* 撤销竖直段时要还原的旧值 */

        r = need - d;
        if (r < 0 || r > 1) continue;  /* 本点凑不出 need 条，换个 d */
        if (d && jd < 0) continue;     /* 要挑“下”，可是下面没有点 */
        if (r && jr < 0) continue;     /* 要挑“右”，可是右边没有点 */

        /* ---- 先判可行性，再落子 ---- */
        if (d && !accept(i, jd)) continue;
        if (r && !accept(i, jr)) continue;

        /* ---- 交叉检查：只查水平段 ---- */
        if (r) {
            int x, ok = 1, row = vr[i];
            for (x = vc[i] + 1; x < vc[jr]; ++x)
                if (vTop[x] < row && vBot[x] > row) { ok = 0; break; }
            if (!ok) continue;
        }

        /* ---------- 落子：一条边要记三笔账 ---------- */
        if (r) {                          /* 往右 */
            deg[jr]++; eR[i] = 1; eL[jr] = 1;
        }
        if (d) {                          /* 往下 */
            deg[jd]++; eD[i] = 1; eU[jd] = 1;
            col = vc[i];
            oldTop = vTop[col]; oldBot = vBot[col];   /* 先存旧值 */
            vTop[col] = vr[i];  vBot[col] = vr[jd];   /* 再覆盖   */
        } /*往右连：扣除双方度数，记录双方的边（双向记账）。
        往下连：扣除双方度数，记录边，并更新扫描线。把 i 和 jd 所在的这一列，竖线的起点和终点记录下来（这样后面处理横线时就能查到了）。*/

        /* ---------- 递归到下一个点 ---------- */
        if (dfs(i + 1)) return 1;

        /* ---------- 撤销：把状态还原成落子之前 ---------- */
        if (d) {
            vTop[col] = oldTop; vBot[col] = oldBot;
            deg[jd]--; eD[i] = 0; eU[jd] = 0;
        }
        if (r) {
            deg[jr]--; eR[i] = 0; eL[jr] = 0;
        }
    }

#ifdef STAT
    fails++;
#endif
    return 0;                 /* 两种 d 都不行：回溯 */
}

/* =====================================================================
 *  main：读入 -> 编号 -> 建候选边 -> 预判 -> 搜索 -> 输出
 * ===================================================================== */
int main(void)
{
    int r, c, i, last, sum = 0;

    if (scanf("%d %d", &n, &m) != 2) return 0;
    for (r = 0; r < n; ++r)
        for (c = 0; c < m; ++c) {
            scanf("%d", &g[r][c]);
            sum += g[r][c];                  /* 总度数（后面判奇偶用） */
        }

    timer_begin = get_time(); /* 修改：调用高精度计时器 */

    /* ---------- 1. 行优先编号 ---------- */
    cnt = 0;
    for (r = 0; r < n; ++r)
        for (c = 0; c < m; ++c) {
            if (g[r][c] > 0) {
                id[r][c] = cnt;
                vr[cnt] = r; vc[cnt] = c; vk[cnt] = g[r][c];
                nxtR[cnt] = nxtD[cnt] = prevR[cnt] = -1;
                deg[cnt] = 0;
                eU[cnt] = eD[cnt] = eL[cnt] = eR[cnt] = 0;
                cnt++;
            } else {
                id[r][c] = -1;               /* 没有连接件 */
            }
        }

    /* ---------- 2. 建候选边 ---------- */
    for (r = 0; r < n; ++r) {
        last = -1;
        for (c = 0; c < m; ++c) {
            if (id[r][c] < 0) continue;
            if (last >= 0) {
                nxtR[last] = id[r][c];
                prevR[id[r][c]] = last;
            }
            last = id[r][c];
        }
    }

    for (c = 0; c < m; ++c) {
        last = -1;
        for (r = 0; r < n; ++r) {
            if (id[r][c] < 0) continue;
            if (last >= 0) nxtD[last] = id[r][c];
            last = id[r][c];
        }
    }

    /* ---------- 3. 两个一眼就能看出的无解 ---------- */
    for (i = 0; i < cnt; ++i) {
        int hasL = (prevR[i] >= 0);
        int hasU = 0, x, rr = vr[i], cc = vc[i];

        for (x = rr - 1; x >= 0; --x)        /* 上方有没有连接件：现扫一遍 */
            if (id[x][cc] >= 0) { hasU = 1; break; }

        /* 度数不能超过“看得见”的方向数 */
        if (vk[i] > hasL + hasU + (nxtR[i] >= 0) + (nxtD[i] >= 0)) {
            report_timing("prog", 0);
            printf("No Solution\n");
            return 0;
        }
    }
    if (sum & 1) {                            /* 握手定理：总度数必须是偶数 */
        report_timing("prog", 0);
        printf("No Solution\n");
        return 0;
    }

    /* ---------- 4. 回溯搜索 ---------- */
    memset(vTop, -1, sizeof(vTop));
    memset(vBot, -1, sizeof(vBot));

    timer_search_begin = get_time(); /* 修改：调用高精度计时器 */
    if (!dfs(0)) {
        report_timing("prog", 1);
        printf("No Solution\n");
        return 0;
    }

    report_timing("prog", 1);

    /* ---------- 5. 输出 ---------- */
    for (i = 0; i < cnt; ++i)
        printf("%d %d %d %d %d %d\n",
               vr[i] + 1, vc[i] + 1, eU[i], eD[i], eL[i], eR[i]);

#ifdef STAT
    fprintf(stderr, "nodes=%lld fails=%lld\n", nodes, fails);
#endif
    return 0;
}
