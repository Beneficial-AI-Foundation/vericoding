datatype Result = Impossible | Possible(cost: int, edges: seq<(int, int)>)

function seq_sum(s: seq<int>): int {
    if |s| == 0 then 0 else s[0] + seq_sum(s[1..])
}

function seq_sum_first(s: seq<int>, n: int): int
    requires 0 <= n <= |s|
{
    if n == 0 then 0 else s[n-1] + seq_sum_first(s, n-1)
}

function min_index(weights: seq<int>): int
    requires |weights| > 0
    ensures 0 <= min_index(weights) < |weights|
    ensures forall j :: 0 <= j < |weights| ==> weights[min_index(weights)] <= weights[j]
{
    min_index_helper(weights, 0, 1)
}

function min_index_helper(weights: seq<int>, current_min: int, next: int): int
    requires |weights| > 0
    requires 0 <= current_min < |weights|
    requires 0 <= next <= |weights|
    requires forall j :: 0 <= j < next ==> weights[current_min] <= weights[j]
    ensures 0 <= min_index_helper(weights, current_min, next) < |weights|
    ensures forall j :: 0 <= j < |weights| ==> weights[min_index_helper(weights, current_min, next)] <= weights[j]
    decreases |weights| - next
{
    if next >= |weights| then current_min
    else if weights[next] < weights[current_min] then min_index_helper(weights, next, next + 1)
    else min_index_helper(weights, current_min, next + 1)
}

function min_index_excluding(weights: seq<int>, exclude: int): int
    requires |weights| > 1
    requires 0 <= exclude < |weights|
    ensures 0 <= min_index_excluding(weights, exclude) < |weights|
    ensures min_index_excluding(weights, exclude) != exclude
    ensures forall j :: 0 <= j < |weights| && j != exclude ==> 
        weights[min_index_excluding(weights, exclude)] <= weights[j]
{
    var first_valid := if exclude == 0 then 1 else 0;
    min_index_excluding_helper(weights, exclude, first_valid, 0)
}

function min_index_excluding_helper(weights: seq<int>, exclude: int, current_min: int, next: int): int
    requires |weights| > 1
    requires 0 <= exclude < |weights|
    requires 0 <= current_min < |weights|
    requires current_min != exclude
    requires 0 <= next <= |weights|
    requires forall j :: 0 <= j < next && j != exclude ==> weights[current_min] <= weights[j]
    ensures 0 <= min_index_excluding_helper(weights, exclude, current_min, next) < |weights|
    ensures min_index_excluding_helper(weights, exclude, current_min, next) != exclude
    ensures forall j :: 0 <= j < |weights| && j != exclude ==> 
        weights[min_index_excluding_helper(weights, exclude, current_min, next)] <= weights[j]
    decreases |weights| - next
{
    if next >= |weights| then current_min
    else if next == exclude then min_index_excluding_helper(weights, exclude, current_min, next + 1)
    else if weights[next] < weights[current_min] then min_index_excluding_helper(weights, exclude, next, next + 1)
    else min_index_excluding_helper(weights, exclude, current_min, next + 1)
}

// <vc-helpers>
lemma min_index_excluding_helper_lemma(weights: seq<int>, exclude: int, current_min: int, next: int)
    requires |weights| > 1
    requires 0 <= exclude < |weights|
    requires 0 <= current_min < |weights|
    requires current_min != exclude
    requires 0 <= next <= |weights|
    requires forall j :: 0 <= j < next && j != exclude ==> weights[current_min] <= weights[j]
    ensures min_index_excluding_helper(weights, exclude, current_min, next) == 
        if next >= |weights| then current_min
        else if next == exclude then min_index_excluding_helper(weights, exclude, current_min, next + 1)
        else if weights[next] < weights[current_min] then min_index_excluding_helper(weights, exclude, next, next + 1)
        else min_index_excluding_helper(weights, exclude, current_min, next + 1)
{
    // This lemma is needed to help Dafny verify the recursive calls
}

lemma min_index_helper_lemma(weights: seq<int>, current_min: int, next: int)
    requires |weights| > 0
    requires 0 <= current_min < |weights|
    requires 0 <= next <= |weights|
    requires forall j :: 0 <= j < next ==> weights[current_min] <= weights[j]
    ensures min_index_helper(weights, current_min, next) == 
        if next >= |weights| then current_min
        else if weights[next] < weights[current_min] then min_index_helper(weights, next, next + 1)
        else min_index_helper(weights, current_min, next + 1)
{
    // This lemma is needed to help Dafny verify the recursive calls
}

lemma min_index_excluding_properties(weights: seq<int>, exclude: int)
    requires |weights| > 1
    requires 0 <= exclude < |weights|
    ensures min_index_excluding(weights, exclude) != exclude
    ensures forall j :: 0 <= j < |weights| && j != exclude ==> 
        weights[min_index_excluding(weights, exclude)] <= weights[j]
{
}

lemma min_index_properties(weights: seq<int>)
    requires |weights| > 0
    ensures 0 <= min_index(weights) < |weights|
    ensures forall j :: 0 <= j < |weights| ==> weights[min_index(weights)] <= weights[j]
{
}
// </vc-helpers>

// <vc-spec>
method solve(t: int, cases: seq<(int, int, seq<int>)>) returns (results: seq<Result>)
    requires t >= 0
    requires |cases| == t
    requires forall i :: 0 <= i < t ==> 
        cases[i].0 >= 0 && cases[i].1 >= 0 && |cases[i].2| == cases[i].0
    ensures |results| == t
    ensures forall i :: 0 <= i < t ==> 
        var n := cases[i].0;
        var m := cases[i].1;
        (n <= 2 || m < n) ==> results[i] == Impossible
    ensures forall i :: 0 <= i < t ==> 
        var n := cases[i].0;
        var m := cases[i].1;
        var weights := cases[i].2;
        (n > 2 && m >= n && results[i].Possible?) ==> 
            |results[i].edges| == m &&
            (forall j :: 0 <= j < |results[i].edges| ==> 
                1 <= results[i].edges[j].0 <= n && 1 <= results[i].edges[j].1 <= n &&
                results[i].edges[j].0 != results[i].edges[j].1)
    ensures forall i :: 0 <= i < t ==> 
        var n := cases[i].0;
        var m := cases[i].1;
        var weights := cases[i].2;
        (n > 2 && m >= n && results[i].Possible?) ==> 
            var min1_idx := min_index(weights);
            var min2_idx := min_index_excluding(weights, min1_idx);
            results[i].cost == 2 * seq_sum(weights) + (m - n) * (weights[min1_idx] + weights[min2_idx])
    ensures forall i :: 0 <= i < t ==> 
        var n := cases[i].0;
        var m := cases[i].1;
        (n > 2 && m >= n && results[i].Possible?) ==> 
            (forall j :: 0 <= j < n ==> 
                results[i].edges[j] == (j + 1, if j == n - 1 then 1 else j + 2)) &&
            (forall j :: n <= j < m ==> 
                var min1_idx := min_index(cases[i].2);
                var min2_idx := min_index_excluding(cases[i].2, min1_idx);
                results[i].edges[j] == (min1_idx + 1, min2_idx + 1))
// </vc-spec>
// <vc-code>
{
    results := [];
    var i := 0;
    while i < t
        invariant |results| == i
        invariant 0 <= i <= t
    {
        var n := cases[i].0;
        var m := cases[i].1;
        var weights := cases[i].2;
        
        if n <= 2 || m < n {
            results := results + [Impossible];
        } else {
            min_index_properties(weights);
            var min1_idx := min_index(weights);
            min_index_excluding_properties(weights, min1_idx);
            var min2_idx := min_index_excluding(weights, min1_idx);
            var min1 := weights[min1_idx];
            var min2 := weights[min2_idx];
            
            // Build the cycle edges (1-2, 2-3, ..., n-1)
            var cycle_edges := [];
            var j := 0;
            while j < n
                invariant |cycle_edges| == j
                invariant 0 <= j <= n
                invariant forall k :: 0 <= k < j ==> 
                    cycle_edges[k] == (k + 1, if k == n - 1 then 1 else k + 2)
            {
                var from := j + 1;
                var to := if j == n - 1 then 1 else j + 2;
                cycle_edges := cycle_edges + [(from, to)];
                j := j + 1;
            }
            
            // Add extra edges connecting the two minimum nodes
            var extra_edges := [];
            j := n;
            while j < m
                invariant |extra_edges| == j - n
                invariant n <= j <= m
                invariant forall k :: 0 <= k < j - n ==> 
                    extra_edges[k] == (min1_idx + 1, min2_idx + 1)
            {
                extra_edges := extra_edges + [(min1_idx + 1, min2_idx + 1)];
                j := j + 1;
            }
            
            var all_edges := cycle_edges + extra_edges;
            var total_cost := 2 * seq_sum(weights) + (m - n) * (min1 + min2);
            results := results + [Possible(total_cost, all_edges)];
        }
        i := i + 1;
    }
}
// </vc-code>

