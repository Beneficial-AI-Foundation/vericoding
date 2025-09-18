// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate AllGreater(n: int, s: seq<int>) { forall i :: 0 <= i < |s| ==> n > s[i] }
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result == (forall i :: 0 <= i < a.Length ==> n > a[i])
// </vc-spec>
// <vc-code>
{
  result := (forall i :: 0 <= i < a.Length ==> n > a[i]);
}
// </vc-code>
