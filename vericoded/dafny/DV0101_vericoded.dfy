// <vc-preamble>
predicate IsSubseqAt(sub: seq<int>, main: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && 
    (forall j :: 0 <= j < |sub| ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> exists i :: IsSubseqAt(sub, main, i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added assertion to help verifier understand empty subsequence case */
  if |sub| == 0 {
    assert IsSubseqAt(sub, main, 0);
    return true;
  }
  if |sub| > |main| {
    return false;
  }
  
  var i := 0;
  while i <= |main| - |sub|
    invariant 0 <= i <= |main| - |sub| + 1
    invariant forall k :: 0 <= k < i ==> !IsSubseqAt(sub, main, k)
  {
    var j := 0;
    var isMatch := true;
    while j < |sub| && isMatch
      invariant 0 <= j <= |sub|
      invariant isMatch ==> forall k :: 0 <= k < j ==> sub[k] == main[i + k]
      invariant !isMatch ==> !IsSubseqAt(sub, main, i)
    {
      if sub[j] != main[i + j] {
        isMatch := false;
      }
      j := j + 1;
    }
    
    if isMatch {
      assert IsSubseqAt(sub, main, i);
      return true;
    }
    i := i + 1;
  }
  
  return false;
}
// </vc-code>
