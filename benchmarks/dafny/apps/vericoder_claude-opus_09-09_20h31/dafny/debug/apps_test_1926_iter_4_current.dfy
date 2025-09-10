predicate ValidInput(n: int, a: seq<int>)
{
  n >= 2 && |a| == n
}

function CountViolationsForK(a: seq<int>, n: int, k: int): int
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
{
  |set i | 2 <= i <= n && 
    var parent_idx := (i + k - 2) / k;
    parent_idx >= 1 && a[i-1] < a[parent_idx-1]|
}

predicate ValidOutput(result: seq<int>, n: int, a: seq<int>)
  requires n >= 2 && |a| == n
{
  |result| == n - 1 &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] >= 0) &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] == CountViolationsForK(a, n, k))
}

// <vc-helpers>
lemma CountViolationsCorrect(a: seq<int>, n: int, k: int, count: int, violating_indices: set<int>)
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
  requires violating_indices == set i | 2 <= i <= n && 
    var parent_idx := (i + k - 2) / k;
    parent_idx >= 1 && a[i-1] < a[parent_idx-1]
  requires count == |violating_indices|
  ensures count == CountViolationsForK(a, n, k)
  ensures count >= 0
{
  // The set comprehension in CountViolationsForK is identical to violating_indices
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: seq<int>)
  requires ValidInput(n, a)
  ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
{
  result := [];
  
  var k := 1;
  while k <= n - 1
    invariant 1 <= k <= n
    invariant |result| == k - 1
    invariant forall j :: 1 <= j < k ==> 0 <= j-1 < |result| && result[j-1] >= 0
    invariant forall j :: 1 <= j < k ==> 0 <= j-1 < |result| && result[j-1] == CountViolationsForK(a, n, j)
  {
    var violations := 0;
    var i := 2;
    
    ghost var violating_indices: set<int> := {};
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant violations >= 0
      invariant violations == |violating_indices|
      invariant violating_indices <= set idx | 2 <= idx <= n
      invariant violating_indices == set idx | 2 <= idx < i && 
        var parent_idx := (idx + k - 2) / k;
        parent_idx >= 1 && a[idx-1] < a[parent_idx-1]
    {
      var parent_idx := (i + k - 2) / k;
      if parent_idx >= 1 && parent_idx <= n && a[i-1] < a[parent_idx-1] {
        ghost var old_violating := violating_indices;
        violating_indices := violating_indices + {i};
        assert |violating_indices| == |old_violating| + 1;
        violations := violations + 1;
      }
      i := i + 1;
    }
    
    assert i == n + 1;
    ghost var final_set := set idx | 2 <= idx <= n && 
        var parent_idx := (idx + k - 2) / k;
        parent_idx >= 1 && a[idx-1] < a[parent_idx-1];
    assert violating_indices == final_set;
    CountViolationsCorrect(a, n, k, violations, violating_indices);
    
    result := result + [violations];
    k := k + 1;
  }
  
  assert k == n;
  assert |result| == n - 1;
}
// </vc-code>

