// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArrayToSeq(a: array<int>) returns (s: seq<int>)
    requires a != null
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Added invariant to prove index safety and postconditions. */
  var i: nat := 0;
  s := [];
  while i < a.Length
    invariant i <= a.Length
    invariant |s| == i
    invariant forall k :: 0 <= k < i ==> s[k] == a[k]
  {
    s := s + [a[i]];
    i := i + 1;
  }
}
// </vc-code>
