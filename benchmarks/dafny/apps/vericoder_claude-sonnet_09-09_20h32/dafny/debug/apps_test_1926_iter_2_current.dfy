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
lemma CountViolationsForKNonNegative(a: seq<int>, n: int, k: int)
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
  ensures CountViolationsForK(a, n, k) >= 0
{
}

lemma CountViolationsForKCorrectness(a: seq<int>, n: int, k: int, violations: int)
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
  requires violations == |set i {:trigger} | 2 <= i <= n && 
    var parent_idx := (i + k - 2) / k;
    parent_idx >= 1 && a[i-1] < a[parent_idx-1]|
  ensures violations == CountViolationsForK(a, n, k)
{
}

lemma SetEquivalence(a: seq<int>, n: int, k: int, i: int)
  requires n >= 2 && |a| == n && 1 <= k <= n - 1 && 2 <= i <= n + 1
  ensures (set idx | 2 <= idx < i && 
    var parent_idx := (idx + k - 2) / k;
    parent_idx >= 1 && a[idx-1] < a[parent_idx-1]) 
  == (set idx | 2 <= idx <= n && 
    var parent_idx := (idx + k - 2) / k;
    parent_idx >= 1 && a[idx-1] < a[parent_idx-1] && idx < i)
{
}

lemma IncrementalCountCorrectness(a: seq<int>, n: int, k: int, i: int, violations: int)
  requires n >= 2 && |a| == n && 1 <= k <= n - 1 && 2 <= i <= n
  requires violations == |set idx | 2 <= idx < i && 
    var parent_idx := (idx + k - 2) / k;
    parent_idx >= 1 && a[idx-1] < a[parent_idx-1]|
  ensures i == n + 1 ==> violations == CountViolationsForK(a, n, k)
{
  if i == n + 1 {
    assert (set idx | 2 <= idx < i && 
      var parent_idx := (idx + k - 2) / k;
      parent_idx >= 1 && a[idx-1] < a[parent_idx-1])
    == (set idx | 2 <= idx <= n && 
      var parent_idx := (idx + k - 2) / k;
      parent_idx >= 1 && a[idx-1] < a[parent_idx-1]);
  }
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
    invariant forall j {:trigger result[j-1]} :: 1 <= j <= k - 1 ==> result[j-1] >= 0
    invariant forall j {:trigger result[j-1]} :: 1 <= j <= k - 1 ==> result[j-1] == CountViolationsForK(a, n, j)
  {
    var violations := 0;
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant violations == |set idx {:trigger} | 2 <= idx < i && 
        var parent_idx := (idx + k - 2) / k;
        parent_idx >= 1 && a[idx-1] < a[parent_idx-1]|
    {
      var parent_idx := (i + k - 2) / k;
      if parent_idx >= 1 && a[i-1] < a[parent_idx-1] {
        violations := violations + 1;
      }
      i := i + 1;
    }
    
    IncrementalCountCorrectness(a, n, k, i, violations);
    assert violations == CountViolationsForK(a, n, k);
    result := result + [violations];
    k := k + 1;
  }
}
// </vc-code>

