// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): basic min helper */
function min(a: int, b: int): int { if a < b then a else b }

/* helper modified by LLM (iteration 5): non-empty sequence predicate */
predicate NonEmptySeq(s: seq<int>) { |s| > 0 }
// </vc-helpers>

// <vc-spec>
method MaxDafnyLsp(a: array<int>) returns (x: int)
    requires a.Length > 0
    ensures 0 <= x < a.Length
    ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[x]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): iterative linear scan to find index of maximum */
  x := 0;
  var i := 1;
  while i < a.Length
    invariant 0 <= x < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] <= a[x]
  {
    if a[i] > a[x] {
      x := i;
    }
    i := i + 1;
  }
}
// </vc-code>
