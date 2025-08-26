method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
{
  if |sub| == 0 {
    result := true;
    return;
  }
  
  if |sub| > |main| {
    result := false;
    return;
  }
  
  var i := 0;
  while i <= |main| - |sub|
    invariant 0 <= i <= |main| - |sub| + 1
    invariant forall j :: 0 <= j < i ==> sub != main[j..j + |sub|]
  {
    if sub == main[i..i + |sub|] {
      result := true;
      assert sub == main[i..i + |sub|] && 0 <= i <= |main| - |sub|;
      assert exists k :: 0 <= k <= |main| - |sub| && sub == main[k..k + |sub|];
      return;
    }
    assert sub != main[i..i + |sub|];
    i := i + 1;
  }
  
  result := false;
  assert i == |main| - |sub| + 1;
  assert forall j :: 0 <= j <= |main| - |sub| ==> sub != main[j..j + |sub|] by {
    forall j | 0 <= j <= |main| - |sub|
      ensures sub != main[j..j + |sub|]
    {
      if j < i {
        assert sub != main[j..j + |sub|];
      } else {
        assert j == |main| - |sub| + 1;
        assert false;
      }
    }
  }
  assert !(exists k :: 0 <= k <= |main| - |sub| && sub == main[k..k + |sub|]);
}
// </vc-code>