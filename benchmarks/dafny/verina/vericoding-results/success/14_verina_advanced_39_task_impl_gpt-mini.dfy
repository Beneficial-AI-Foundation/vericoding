// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): recursive max over a non-empty sequence */
function MaxSeq(s: seq<nat>): nat
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && s[i] == MaxSeq(s)
  ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxSeq(s)
  decreases |s|
{
  if |s| == 1 then s[0] else if s[0] > MaxSeq(s[1..]) then s[0] else MaxSeq(s[1..])
}
// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<nat>) returns (result: nat)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute max iteratively with invariants */
  var i := 1;
  result := lst[0];
  while i < lst.Length
    invariant 1 <= i <= lst.Length
    invariant exists j :: 0 <= j < i && lst[j] == result
    invariant forall j :: 0 <= j < i ==> lst[j] <= result
  {
    if lst[i] > result {
      result := lst[i];
    }
    i := i + 1;
  }
}
// </vc-code>
