//IMPL SmallestMissingNumber
method SmallestMissingNumber(s: seq<int>) returns (v: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures 0 <= v
  ensures v !in s
  ensures forall k :: 0 <= k < v ==> k in s
{
  v := 0;
  var i := 0;
  
  while i < |s|
    /* code modified by LLM (iteration 1): strengthened loop invariants to maintain all necessary properties */
    invariant 0 <= i <= |s|
    invariant 0 <= v
    invariant forall k :: 0 <= k < v ==> k in s
    invariant forall j :: 0 <= j < i ==> s[j] < v
    invariant v !in s[0..i]
  {
    if s[i] == v {
      /* code modified by LLM (iteration 1): added assertion to help verification */
      assert v in s;
      v := v + 1;
    } else if s[i] > v {
      /* code modified by LLM (iteration 1): added assertions to justify early return */
      assert v !in s[0..i];
      assert forall j :: i <= j < |s| ==> s[j] >= s[i] > v;
      assert v !in s[i..];
      assert v !in s;
      return;
    }
    /* code modified by LLM (iteration 1): added assertion to help maintain invariant */
    assert s[i] < v;
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): added final assertion to establish postcondition */
  assert v !in s[0..i];
  assert i == |s|;
  assert v !in s;
}