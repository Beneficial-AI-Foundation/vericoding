function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
lemma popcount_nonnegative(n: nat)
  ensures popcount(n) >= 0
{
}

lemma popcount_bounds(n: nat)
  ensures popcount(n) <= n
{
  if n == 0 {
  } else {
    popcount_bounds(n / 2);
  }
}

lemma multiset_insert_preserves(s1: seq<nat>, s2: seq<nat>, elem: nat, pos: int)
  requires 0 <= pos <= |s1|
  requires s2 == s1[..pos] + [elem] + s1[pos..]
  ensures multiset(s2) == multiset(s1) + multiset([elem])
{
}

lemma multiset_slice_property(arr: seq<nat>, k: int)
  requires 0 <= k <= |arr|
  ensures multiset(arr[..k] + [arr[k]]) == multiset(arr[..k+1]) when k < |arr|
{
}

method insertion_sort_by_popcount(arr: seq<nat>) returns (result: seq<nat>)
  ensures |result| == |arr|
  ensures multiset(arr) == multiset(result)
  ensures forall i, j :: 0 <= i < j < |result| ==> popcount(result[i]) <= popcount(result[j])
{
  if |arr| == 0 {
    return [];
  }
  
  result := [arr[0]];
  
  for k := 1 to |arr|
    invariant 1 <= k <= |arr|
    invariant |result| == k
    invariant multiset(result) == multiset(arr[..k])
    invariant forall i, j :: 0 <= i < j < |result| ==> popcount(result[i]) <= popcount(result[j])
  {
    var elem := arr[k];
    var old_result := result;
    var pos := 0;
    
    while pos < |result| && popcount(result[pos]) <= popcount(elem)
      invariant 0 <= pos <= |result|
      invariant forall i :: 0 <= i < pos ==> popcount(result[i]) <= popcount(elem)
      invariant result == old_result
    {
      pos := pos + 1;
    }
    
    result := result[..pos] + [elem] + result[pos..];
    multiset_insert_preserves(old_result, result, elem, pos);
    assert multiset(result) == multiset(old_result) + multiset([elem]);
    assert multiset(old_result) == multiset(arr[..k]);
    assert elem == arr[k];
    multiset_slice_property(arr, k);
    assert multiset(arr[..k] + [arr[k]]) == multiset(arr[..k+1]);
    assert multiset(result) == multiset(arr[..k+1]);
  }
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := insertion_sort_by_popcount(s);
}
// </vc-code>

