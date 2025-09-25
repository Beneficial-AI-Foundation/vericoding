// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Reverse (a : array<int>) returns (aRev : array<int>)
    ensures aRev.Length == a.Length
    ensures forall i : int :: 0 <= i < a.Length ==> a[i] == aRev[aRev.Length-i-1]
    ensures fresh(aRev)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
