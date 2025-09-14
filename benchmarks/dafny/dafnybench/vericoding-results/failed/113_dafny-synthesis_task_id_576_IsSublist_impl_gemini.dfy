// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implemented lemma to prove the induction step */
lemma NoSublistStep(sub: seq<int>, main: seq<int>, i: int)
  requires 0 <= i
  requires i + |sub| <= |main|
  requires forall k :: 0 <= k < i ==> sub != main[k..k+|sub|]
  requires sub != main[i..i+|sub|]
  ensures forall k :: 0 <= k < i + 1 ==> sub != main[k..k+|sub|]
{
  forall k | 0 <= k < i + 1 
    ensures sub != main[k..k+|sub|]
  {
  }
}
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): called helper lemma to maintain loop invariant */
{
  if |sub| > |main| {
    result := false;
    return;
  }

  var i := 0;
  while i <= |main| - |sub|
    invariant 0 <= i <= |main| - |sub| + 1
    invariant forall k :: 0 <= k < i ==> sub != main[k..k+|sub|]
  {
    if main[i..i+|sub|] == sub {
      result := true;
      return;
    }
    NoSublistStep(sub, main, i);
    i := i + 1;
  }

  result := false;
}
// </vc-code>
