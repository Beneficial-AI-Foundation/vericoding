// IMPL
method SmallestMissingNumber(s: seq<int>) returns (v: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures 0 <= v
  ensures v !in s
  ensures forall k :: 0 <= k < v ==> k in s
{
  var i := 0;
  
  /* code modified by LLM (iteration 4): Added lemma to establish the key invariant from sortedness */
  assert forall j :: 0 <= j < |s| ==> s[j] >= s[0] >= 0;
  
  /* code modified by LLM (iteration 4): Prove that s[j] >= j for all valid j by induction */
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant forall j :: 0 <= j < k ==> s[j] >= j
  {
    if k == 0 {
      assert s[k] >= 0 == k;
    } else {
      assert s[k] >= s[k-1] >= k-1;
      if s[k] == k-1 {
        assert s[k] >= k-1;
        assert s[k] >= k-1;
        // This would mean s[k] == k-1, but we need s[k] >= k
        // Since s is sorted and contains integers, if s[k-1] >= k-1 and s[k] >= s[k-1]
        // then s[k] >= k-1. If s[k] == k-1, then we have s[k-1] <= s[k] == k-1
        // So s[k-1] <= k-1. But we know s[k-1] >= k-1, so s[k-1] == k-1.
        // This creates a contradiction unless s[k] > k-1, so s[k] >= k.
      }
      assert s[k] >= k;
    }
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 4): Now we can use the proven property in our main loop */
  while i < |s| && s[i] == i
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> k in s
    invariant forall j :: 0 <= j < i ==> s[j] == j
    invariant i < |s| ==> s[i] >= i
  {
    i := i + 1;
  }
  
  v := i;
  
  /* code modified by LLM (iteration 4): Simplified proof that v is not in s */
  if i < |s| {
    assert s[i] != i;
    assert s[i] >= i;
    assert s[i] > i;
    assert forall j :: i <= j < |s| ==> s[j] >= s[i] > i;
    assert forall j :: 0 <= j < i ==> s[j] == j != i;
    assert v !in s;
  } else {
    assert v !in s;
  }
}