// <vc-preamble>
predicate IsSubrangeAt(main: seq<int>, sub: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && sub == main[i..i+|sub|]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): helper to verify array equality at position */
lemma ArrayMatchImpliesSubrange(main: array<int>, sub: array<int>, i: int)
    requires 0 <= i <= main.Length - sub.Length
    requires forall idx :: 0 <= idx < sub.Length ==> main[i + idx] == sub[idx]
    ensures IsSubrangeAt(main[..], sub[..], i)
{
    assert sub[..] == main[i..i+sub.Length];
}
// </vc-helpers>

// <vc-spec>
method IsSubArray(main: array<int>, sub: array<int>) returns (result: bool)
    ensures result == (exists k :: 0 <= k <= (main.Length - sub.Length) && IsSubrangeAt(main[..], sub[..], k))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed postcondition proof with lemma */
{
  if sub.Length > main.Length {
    result := false;
    return;
  }
  
  var i := 0;
  while i <= main.Length - sub.Length
    invariant 0 <= i <= main.Length - sub.Length + 1
    invariant forall k :: 0 <= k < i ==> !IsSubrangeAt(main[..], sub[..], k)
  {
    var j := 0;
    var matches := true;
    while j < sub.Length && matches
      invariant 0 <= j <= sub.Length
      invariant matches ==> forall idx :: 0 <= idx < j ==> main[i + idx] == sub[idx]
      invariant !matches ==> exists idx :: 0 <= idx < j && main[i + idx] != sub[idx]
    {
      if main[i + j] != sub[j] {
        matches := false;
      }
      j := j + 1;
    }
    
    if matches {
      ArrayMatchImpliesSubrange(main, sub, i);
      result := true;
      return;
    }
    
    i := i + 1;
  }
  
  result := false;
}
// </vc-code>
