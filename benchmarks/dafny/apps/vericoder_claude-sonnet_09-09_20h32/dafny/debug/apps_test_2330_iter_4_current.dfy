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
lemma seq_sum_property(s: seq<int>)
    ensures seq_sum(s) == seq_sum_first(s, |s|)
{
    if |s| == 0 {
        assert seq_sum(s) == 0;
        assert seq_sum_first(s, 0) == 0;
    } else {
        seq_sum_property(s[1..]);
        assert seq_sum(s[1..]) == seq_sum_first(s[1..], |s[1..]|);
        assert |s[1..]| == |s| - 1;
        assert seq_sum(s) == s[0] + seq_sum(s[1..]);
        assert seq_sum_first(s, |s|) == s[|s|-1] + seq_sum_first(s, |s|-1);
        seq_sum_first_shift(s, |s|);
        assert seq_sum_first(s, |s|-1) == seq_sum_first(s[1..], |s|-1);
        assert seq_sum_first(s[1..], |s|-1) == seq_sum_first(s[1..], |s[1..]|);
        assert s[0] == s[|s|-1] by {
            // This assertion helps Dafny understand the connection
            assert |s| >= 1;
        }
    }
}

lemma seq_sum_first_relation(s: seq<int>, n: int)
    requires 0 < n <= |s|
    ensures seq_sum_first(s, n) == s[n-1] + seq_sum_first(s, n-1)
{
    // This follows directly from the definition of seq_sum_first
}

lemma seq_sum_first_shift(s: seq<int>, n: int)
    requires 0 < n <= |s|
    ensures seq_sum_first(s, n-1) == seq_sum_first(s[1..], n-1)
{
    if n == 1 {
        assert seq_sum_first(s, 0) == 0;
        assert seq_sum_first(s[1..], 0) == 0;
    } else {
        assert n > 1;
        assert seq_sum_first(s, n-1) == s[n-2] + seq_sum_first(s, n-2);
        assert seq_sum_first(s[1..], n-1) == s[1..][(n-1)-1] + seq_sum_first(s[1..], (n-1)-1);
        assert s[1..][(n-1)-1] == s[1..][n-2] == s[n-1];
        assert s[n-2] == s[n-1] by {
            // This needs to be proven based on the specific structure
            seq_sum_first_shift(s, n-1);
        }
    }
}

lemma min_index_properties(weights: seq<int>)
    requires |weights| > 1
    ensures var min1 := min_index(weights);
            var min2 := min_index_excluding(weights, min1);
            min1 != min2 && 0 <= min1 < |weights| && 0 <= min2 < |weights|
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
        invariant 0 <= i <= t
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            var n := cases[j].0;
            var m := cases[j].1;
            (n <= 2 || m < n) ==> results[j] == Impossible
        invariant forall j :: 0 <= j < i ==> 
            var n := cases[j].0;
            var m := cases[j].1;
            var weights := cases[j].2;
            (n > 2 && m >= n && results[j].Possible?) ==> 
                |results[j].edges| == m &&
                (forall k :: 0 <= k < |results[j].edges| ==> 
                    1 <= results[j].edges[k].0 <= n && 1 <= results[j].edges[k].1 <= n &&
                    results[j].edges[k].0 != results[j].edges[k].1)
        invariant forall j :: 0 <= j < i ==> 
            var n := cases[j].0;
            var m := cases[j].1;
            var weights := cases[j].2;
            (n > 2 && m >= n && results[j].Possible?) ==> 
                var min1_idx := min_index(weights);
                var min2_idx := min_index_excluding(weights, min1_idx);
                results[j].cost == 2 * seq_sum(weights) + (m - n) * (weights[min1_idx] + weights[min2_idx])
        invariant forall j :: 0 <= j < i ==> 
            var n := cases[j].0;
            var m := cases[j].1;
            (n > 2 && m >= n && results[j].Possible?) ==> 
                (forall k :: 0 <= k < n ==> 
                    results[j].edges[k] == (k + 1, if k == n - 1 then 1 else k + 2)) &&
                (forall k :: n <= k < m ==> 
                    var min1_idx := min_index(cases[j].2);
                    var min2_idx := min_index_excluding(cases[j].2, min1_idx);
                    results[j].edges[k] == (min1_idx + 1, min2_idx + 1))
    {
        var n := cases[i].0;
        var m := cases[i].1;
        var weights := cases[i].2;
        
        if n <= 2 || m < n {
            results := results + [Impossible];
        } else {
            seq_sum_property(weights);
            var min1_idx := min_index(weights);
            var min2_idx := min_index_excluding(weights, min1_idx);
            var cost := 2 * seq_sum(weights) + (m - n) * (weights[min1_idx] + weights[min2_idx]);
            
            var edges: seq<(int, int)> := [];
            var j := 0;
            
            while j < n
                invariant 0 <= j <= n
                invariant |edges| == j
                invariant forall k :: 0 <= k < j ==> 
                    edges[k] == (k + 1, if k == n - 1 then 1 else k + 2)
            {
                var next := if j == n - 1 then 1 else j + 2;
                edges := edges + [(j + 1, next)];
                j := j + 1;
            }
            
            j := n;
            while j < m
                invariant n <= j <= m
                invariant |edges| == j
                invariant forall k :: 0 <= k < n ==> 
                    edges[k] == (k + 1, if k == n - 1 then 1 else k + 2)
                invariant forall k :: n <= k < j ==> 
                    edges[k] == (min1_idx + 1, min2_idx + 1)
            {
                edges := edges + [(min1_idx + 1, min2_idx + 1)];
                j := j + 1;
            }
            
            results := results + [Possible(cost, edges)];
        }
        
        i := i + 1;
    }
}
// </vc-code>

