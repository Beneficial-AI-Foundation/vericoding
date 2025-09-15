// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate AllBelow(l: seq<int>, t: int) { forall i: int :: i >= 0 && i < |l| ==> l[i] < t }
// </vc-helpers>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)

    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
// </vc-spec>
// <vc-code>
{
  b := (forall i: int :: i >= 0 && i < |l| ==> l[i] < t);
}
// </vc-code>
