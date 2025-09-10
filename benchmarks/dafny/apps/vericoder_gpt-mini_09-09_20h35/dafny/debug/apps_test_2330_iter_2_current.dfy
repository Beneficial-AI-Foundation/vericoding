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
// Added no additional helpers.
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
  var idx := 0;
  results := [];
  while idx < t
    invariant 0 <= idx <= t
    invariant |results| == idx
    invariant forall ii :: 0 <= ii < idx ==>
      var n0 := cases[ii].0;
      var m0 := cases[ii].1;
      var w0 := cases[ii].2;
      (n0 <= 2 || m0 < n0) ==> results[ii] == Impossible
    invariant forall ii :: 0 <= ii < idx ==>
      var n0 := cases[ii].0;
      var m0 := cases[ii].1;
      var w0 := cases[ii].2;
      (n0 > 2 && m0 >= n0 && results[ii].Possible?) ==>
        |results[ii].edges| == m0 &&
        (forall j0 :: 0 <= j0 < |results[ii].edges| ==>
           1 <= results[ii].edges[j0].0 <= n0 &&
           1 <= results[ii].edges[j0].1 <= n0 &&
           results[ii].edges[j0].0 != results[ii].edges[j0].1) &&
        var min1_idx := min_index(w0);
        var min2_idx := min_index_excluding(w0, min1_idx);
        results[ii].cost == 2 * seq_sum(w0) + (m0 - n0) * (w0[min1_idx] + w0[min2_idx]) &&
        (forall j0 :: 0 <= j0 < n0 ==>
           results[ii].edges[j0] == (j0 + 1, if j0 == n0 - 1 then 1 else j0 + 2)) &&
        (forall j0 :: n0 <= j0 < m0 ==>
           results[ii].edges[j0] == (min1_idx + 1, min2_idx + 1))
  {
    var n := cases[idx].0;
    var m := cases[idx].1;
    var weights := cases[idx].2;
    if n <= 2 || m < n {
      results := results + [Impossible];
    } else {
      var edges: seq<(int,int)> := [];
      var j := 0;
      while j < n
        invariant 0 <= j <= n
        invariant |edges| == j
        invariant forall jj :: 0 <= jj < j ==>
          edges[jj] == (jj + 1, if jj == n - 1 then 1 else jj + 2)
        invariant forall jj :: 0 <= jj < j ==>
          1 <= edges[jj].0 <= n && 1 <= edges[jj].1 <= n && edges[jj].0 != edges[jj].1
      {
        var e := if j == n - 1 then (j + 1, 1) else (j + 1, j + 2);
        edges := edges + [e];
        j := j + 1;
      }
      var min1 := min_index(weights);
      var min2 := min_index_excluding(weights, min1);
      var k := n;
      while k < m
        invariant n <= k <= m
        invariant |edges| == k
        invariant forall jj :: 0 <= jj < n ==>
          edges[jj] == (jj + 1, if jj == n - 1 then 1 else jj + 2)
        invariant forall jj :: n <= jj < k ==>
          edges[jj] == (min1 + 1, min2 + 1)
        invariant forall jj :: 0 <= jj < k ==>
          1 <= edges[jj].0 <= n && 1 <= edges[jj].1 <= n && edges[jj].0 != edges[jj].1
      {
        edges := edges + [(min1 + 1, min2 + 1)];
        k := k + 1;
      }
      var cost := 2 * seq_sum(weights) + (m - n) * (weights[min1] + weights[min2]);
      results := results + [Possible(cost, edges)];
    }
    idx := idx + 1;
  }
}
// </vc-code>

