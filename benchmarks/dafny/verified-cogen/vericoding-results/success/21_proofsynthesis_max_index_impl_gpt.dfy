// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): implemented recursive max-index over prefix without let-binding and using int parameter to avoid nat casting issues */
function MaxIndexOfPrefix(s: seq<int>, i: int): int
  requires 1 <= i <= |s|
  ensures 0 <= MaxIndexOfPrefix(s, i) < i
  ensures forall k :: 0 <= k < i ==> s[MaxIndexOfPrefix(s, i)] >= s[k]
  decreases i
{
  if i == 1 then 0
  else if s[i - 1] >= s[MaxIndexOfPrefix(s, i - 1)] then i - 1
  else MaxIndexOfPrefix(s, i - 1)
}
// </vc-helpers>

// <vc-spec>
method MyFun1(x: array<int>) returns (max_index: int)
    requires x.Length >= 1
    ensures 0 <= max_index < x.Length
    ensures forall k :: 0 <= k < x.Length ==> x[max_index] >= x[k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented linear scan to find max index with loop invariants */
  var m := 0;
  var i := 1;
  while i < x.Length
    invariant 0 <= m < i <= x.Length
    invariant forall k :: 0 <= k < i ==> x[m] >= x[k]
    decreases x.Length - i
  {
      if x[i] > x[m] {
          m := i;
      }
      i := i + 1;
  }
  max_index := m;
}
// </vc-code>
