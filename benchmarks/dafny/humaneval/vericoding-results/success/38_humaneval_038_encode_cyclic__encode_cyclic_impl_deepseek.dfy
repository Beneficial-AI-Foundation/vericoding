// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function cyclicElement(s: seq<int>, i: int): int
  requires 0 <= i < |s| - |s| % 3
  ensures cyclicElement(s, i) == (
    if i % 3 == 0 then s[i + 1]
    else if i % 3 == 1 then s[i + 1]
    else s[i - 2])
{
  if i % 3 == 0 then s[i + 1]
  else if i % 3 == 1 then s[i + 1]
  else s[i - 2]
}

lemma CyclicShiftLemma(s: seq<int>, i: int)
  requires 0 <= i <= |s| - 3
  requires i % 3 == 0
{
  // This lemma is not actually needed, so we leave it empty
}

lemma GroupPreservationLemma(s: seq<int>, boundary: int)
  requires 0 <= boundary <= |s|
{
  // This lemma is not actually needed, so we leave it empty
}
// </vc-helpers>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>) 

    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): simplified implementation using cyclicElement helper */
  var boundary := |s| - |s| % 3;
  res := [];
  var i := 0;
  
  while i < boundary
    invariant 0 <= i <= boundary
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == cyclicElement(s, k)
  {
    res := res + [cyclicElement(s, i)];
    i := i + 1;
  }
  
  while i < |s|
    invariant boundary <= i <= |s|
    invariant |res| == i
    invariant forall k :: 0 <= k < boundary ==> res[k] == cyclicElement(s, k)
    invariant forall k :: boundary <= k < i ==> res[k] == s[k]
  {
    res := res + [s[i]];
    i := i + 1;
  }
}
// </vc-code>
