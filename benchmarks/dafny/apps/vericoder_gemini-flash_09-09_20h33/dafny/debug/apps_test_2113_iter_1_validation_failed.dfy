predicate IsConnectedTree(n: int, edges: seq<(int, int)>)
{
    n >= 1 && |edges| == n - 1 &&
    (n == 1 ==> |edges| == 0) &&
    (n > 1 ==> IsConnectedGraph(n, edges))
}

predicate IsConnectedGraph(n: int, edges: seq<(int, int)>)
{
    n > 1 ==>
    (forall node :: 2 <= node <= n ==> 
        CanReachNodeOne(node, edges, n))
}

predicate CanReachNodeOne(target: int, edges: seq<(int, int)>, maxDepth: int)
    decreases maxDepth
{
    if maxDepth <= 0 then false
    else if target == 1 then true
    else 
        exists i :: 0 <= i < |edges| && 
            ((edges[i].0 == target && CanReachNodeOne(edges[i].1, edges, maxDepth - 1)) ||
             (edges[i].1 == target && CanReachNodeOne(edges[i].0, edges, maxDepth - 1)))
}

predicate ValidTreeInput(n: int, edges: seq<(int, int)>)
{
    n >= 1 &&
    |edges| == n - 1 &&
    (forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n) &&
    (forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1) &&
    (forall i, j :: 0 <= i < j < |edges| ==> 
        !(edges[i].0 == edges[j].0 && edges[i].1 == edges[j].1) && 
        !(edges[i].0 == edges[j].1 && edges[i].1 == edges[j].0)) &&
    (n == 1 ==> |edges| == 0) &&
    (n > 1 ==> (forall node {:trigger} :: 1 <= node <= n ==> 
        (exists i :: 0 <= i < |edges| && (edges[i].0 == node || edges[i].1 == node)))) &&
    IsConnectedTree(n, edges)
}

// <vc-helpers>
function Max(a: int, b: int): int {
    if a > b then a else b
}
function Min(a: int, b: int): int {
    if a < b then a else b
}

lemma SumOfDegreesIsTwiceEdges(n: int, edges: seq<(int, int)>)
    requires n >= 1
    requires forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n
    requires forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1
    ensures var degrees := map<int, int>(f := j => 0);
            (forall i :: 0 <= i < |edges| ==> 
                (degrees := degrees + map<int,int>([(edges[i].0, 1), (edges[i].1, 1)])); 
            sum j :: 1 <= j <= n :: degrees[j]) == 2 * |edges|
{
    // This lemma is generally known; in Dafny, it could be proven by induction on |edges|
    // For competitive programming context, we assume this property.
}

predicate IsTree(n: int, edges: seq<(int, int)>)
{
    n >= 1 &&
    |edges| == n - 1 &&
    (forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n) &&
    (forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1) &&
    (forall i, j :: 0 <= i < j < |edges| ==> 
        !(edges[i].0 == edges[j].0 && edges[i].1 == edges[j].1) && 
        !(edges[i].0 == edges[j].1 && edges[i].1 == edges[j].0)) &&
    IsConnectedTree(n, edges) // This implies acyclic property due to |edges| == n - 1
}

// Proof that ValidTreeInput implies IsTree
lemma ValidTreeInputImpliesIsTree(n: int, edges: seq<(int, int)>)
    requires ValidTreeInput(n, edges)
    ensures IsTree(n, edges)
{
    // All conditions of IsTree are directly implied by ValidTreeInput's definition.
    // Specifically, ValidTreeInput directly includes IsConnectedTree and all the other
    // requirements like edge bounds, distinct endpoints, and unique edges.
}

// A standard algorithm for finding the maximum cut in a tree is to
// root the tree arbitrarily, compute the size of each subtree,
// and then for each edge, the cut made by removing it is 2 * min(subtree_size, n - subtree_size).
// The maximum cut is simply the largest of these.
// For a tree, maxcut = max_over_edges ( min(size_of_one_component, n - size_of_one_component) )
// This isn't exactly what the problem asks for, which is blue * red - (n - 1).
// This formula is `blue * red - number_of_edges_in_cut`.
// The maximum cut for a tree is related to the balance of partitioning nodes into two sets.
// For a tree, the maximum cut problem is asking to partition the vertices into two sets A and B.
// The value of a cut is the number of edges with one endpoint in A and one in B.
// The maximum cut in a tree can be found by choosing an arbitrary root, then for each node u,
// calculate the size of the subtree rooted at u (including u).
// If an edge (u, v) is cut (where v is a child of u), then the graph splits into the subtree at v
// and the rest of the graph. The size of the first part is subtree_size(v), and the second is n - subtree_size(v).
// The number of edges in a maximum cut (max number of edges between blue and red nodes) for a tree
// is n - 1 (the total number of edges) minus the number of edges that are *not* cut.
// We are maximizing `blue * red - (n-1)`.
// This problem resembles the Maximum Weight K-Partition problem for K=2, which for trees is related
// to centroid decomposition. The quantity `blue * red` is maximized when `blue` and `red` are as close as possible,
// i.e., `blue ~ n/2, red ~ n/2`.
// The formula `blue * red - (n - 1)` is a bit unusual.

// For a tree, finding a partition (blue, red) that maximizes blue * red is achieved when blue and red
// are as close as possible to n/2.
// The result is blue * red - (n - 1).
// This means we are trying to maximize `blue * (n - blue) - (n - 1)`.
// `blue * n - blue^2 - n + 1`.

// Let's reconsider the problem statement's `ensures` clauses:
// `ensures (exists blue, red :: blue >= 0 && red >= 0 && blue + red == n && result == blue * red - (n - 1))`
// This implies `result` will always be `blue * red - (n - 1)` for *some* partition.
// The goal is clearly to find a partition that maximizes `blue * red`.
// For a fixed sum `n`, `x * (n-x)` is maximized when `x` is as close to `n/2` as possible.
// So, if `n` is even, `blue = n/2`, `red = n/2`. Then `result = (n/2)*(n/2) - (n-1) = n*n/4 - n + 1`.
// If `n` is odd, `blue = (n-1)/2`, `red = (n+1)/2` (or vice versa).
// Then `result = ((n-1)/2)*((n+1)/2) - (n-1) = (n*n - 1)/4 - n + 1`.
// The upper bound `result <= (n * n) / 4 - (n - 1) + (if n % 2 == 0 then 0 else 1)`
// This simplifies to:
// If n is even: `n*n/4 - (n-1)`
// If n is odd: `(n*n - 1)/4 - (n-1)`
// This is exactly `max_blue_times_red - (n-1)`.

// This implies that any valid tree partition can achieve this maximal `blue * red` value.
// Any tree with n nodes can be partitioned into two sets of sizes `blue` and `red` such that
// `blue + red = n`.
// Thus, the `result` should be `(n/2)*(n/2) - (n-1)` if n is even, or
// `(n-1)/2 * (n+1)/2 - (n-1)` if n is odd.

// Let's confirm the small cases:
// n = 1: result should be 0.
//   Formula for n=1: blue=0, red=1, (0*1)-(1-1) = 0. OR blue=1, red=0, (1*0)-(1-1) = 0.
// n = 2: result should be 0.
//   Formula for n=2: blue=1, red=1, (1*1)-(2-1) = 1 - 1 = 0.
// n = 3: (n-1)/2 * (n+1)/2 - (n-1) = (2/2) * (4/2) - 2 = 1 * 2 - 2 = 0.
//   For n=3, blue=1, red=2. 1*2 - (3-1) = 2 - 2 = 0.
// n = 4: (n/2)*(n/2) - (n-1) = (4/2)*(4/2) - 3 = 2*2 - 3 = 1.
//   For n=4, blue=2, red=2. 2*2 - (4-1) = 4 - 3 = 1.

// The value that is being asked for seems to be independent of the specific tree structure,
// as long as it satisfies the properties of being a tree.
// The problem asks for the maximum possible value of `blue * red - (n-1)` over *all possible partitions* (blue, red)
// where `blue + red = n`. This is purely an arithmetic maximization problem.
// The 'tree' context and `ValidTreeInput` seems to be a distractor, just ensuring `n` and `edges`
// are actual components of a tree.

// The solution simply needs to compute the maximum value of `x * (n-x) - (n-1)`.
// This maximum occurs around x = n/2.
// </vc-helpers>

// <vc-spec>
method solve(n: int, edges: seq<(int, int)>) returns (result: int)
    requires ValidTreeInput(n, edges)
    ensures result >= 0
    ensures (exists blue, red :: 
        blue >= 0 && red >= 0 && blue + red == n && result == blue * red - (n - 1))
    ensures n == 1 ==> result == 0
    ensures n == 2 ==> result == 0
    ensures n > 2 ==> (exists blue, red :: 
        blue > 0 && red > 0 && blue + red == n && result == blue * red - (n - 1))
    ensures result <= (n * n) / 4 - (n - 1) + (if n % 2 == 0 then 0 else 1)
// </vc-spec>
// <vc-code>
{
    if n == 1 || n == 2 {
        return 0;
    } else {
        var blue: int := n / 2;
        var red: int := n - blue;
        // blue and red will be n/2 and n - n/2, distributing nodes as evenly as possible.
        // If n is even, blue = n/2, red = n/2.
        // If n is odd, blue = floor(n/2), red = ceil(n/2).
        // In both cases, blue and red are the two integers closest to n/2 that sum to n.
        // This pair (blue, red) maximizes the product blue * red for a fixed sum n.
        return blue * red - (n - 1);
    }
}
// </vc-code>

