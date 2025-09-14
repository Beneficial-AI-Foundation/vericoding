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
// no helpers needed
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
  var res: seq<Result> := [];
  var i := 0;
  while i < t
    invariant 0 <= i <= t
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==>
      (
        var n := cases[k].0;
        var m := cases[k].1;
        var weights := cases[k].2;
        if n <= 2 || m < n then
          res[k] == Impossible
        else
          res[k].Possible? &&
          |res[k].edges| == m &&
          (forall j :: 0 <= j < n ==> res[k].edges[j] == (j + 1, if j == n - 1 then 1 else j + 2)) &&
          (forall j :: n <= j < m ==>
            var min1_idx := min_index(weights);
            var min2_idx := min_index_excluding(weights, min1_idx);
            res[k].edges[j] == (min1_idx + 1, min2_idx + 1)) &&
          (forall j :: 0 <= j < |res[k].edges| ==>
            1 <= res[k].edges[j].0 <= n &&
            1 <= res[k].edges[j].1 <= n &&
            res[k].edges[j].0 != res[k].edges[j].1) &&
          res[k].cost ==
            (2 * seq_sum(weights) +
             (m - n) * (weights[min_index(weights)] + weights[min_index_excluding(weights, min_index(weights))]))
      )
    decreases t - i
  {
    var n := cases[i].0;
    var m := cases[i].1;
    var weights := cases[i].2;
    if n <= 2 || m < n {
      res := res + [Impossible];
    } else {
      var min1 := min_index(weights);
      var min2 := min_index_excluding(weights, min1);
      var edges: seq<(int, int)> := [];
      var j := 0;
      while j < n
        invariant 0 <= j <= n
        invariant |edges| == j
        invariant forall k :: 0 <= k < j ==> edges[k] == (k + 1, if k == n - 1 then 1 else k + 2)
        invariant forall k :: 0 <= k < j ==> 1 <= edges[k].0 <= n && 1 <= edges[k].1 <= n && edges[k].0 != edges[k].1
        decreases n - j
      {
        var p0 := j + 1;
        var p1 := if j == n - 1 then 1 else j + 2;

        // bounds and distinctness for new edge
        assert 1 <= p0;
        assert p0 <= n; // since j < n, j+1 <= n
        if j == n - 1 {
          assert p1 == 1;
          assert p0 == n;
          assert n > 2;
          assert p0 != p1;
        } else {
          assert j < n - 1 ==> j + 2 <= n;
          assert p1 <= n;
          assert j + 1 < j + 2;
          assert p0 != p1;
        }
        assert 1 <= p1;

        edges := edges + [(p0, p1)];
        j := j + 1;
      }

      var j2 := n;
      while j2 < m
        invariant n <= j2 <= m
        invariant |edges| == j2
        invariant forall k :: 0 <= k < n ==> edges[k] == (k + 1, if k == n - 1 then 1 else k + 2)
        invariant forall k :: n <= k < j2 ==> edges[k] == (min1 + 1, min2 + 1)
        invariant forall k :: 0 <= k < j2 ==> 1 <= edges[k].0 <= n && 1 <= edges[k].1 <= n && edges[k].0 != edges[k].1
        decreases m - j2
      {
        // show new edge is valid and within range
        assert 0 <= min1 < n;
        assert 0 <= min2 < n;
        assert min1 != min2;
        assert 1 <= min1 + 1 <= n;
        assert 1 <= min2 + 1 <= n;
        assert min1 + 1 != min2 + 1;

        edges := edges + [(min1 + 1, min2 + 1)];
        j2 := j2 + 1;
      }

      var cost := 2 * seq_sum(weights) + (m - n) * (weights[min1] + weights[min2]);
      res := res + [Possible(cost, edges)];
    }
    i := i + 1;
  }
  results := res;
}
// </vc-code>

