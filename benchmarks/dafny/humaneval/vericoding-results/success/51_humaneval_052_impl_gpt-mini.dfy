// <vc-preamble>

predicate BelowThreshold(l: seq<int>, t: int)
{
    forall i :: 0 <= i < |l| ==> l[i] < t
}
// </vc-preamble>

// <vc-helpers>
function AllBelow(l: seq<int>, t: int): bool {
    forall i :: 0 <= i < |l| ==> l[i] < t
}
// </vc-helpers>

// <vc-spec>
method CheckBelowThreshold(l: seq<int>, t: int) returns (result: bool)
    ensures result == BelowThreshold(l, t)
// </vc-spec>
// <vc-code>
{
  result := AllBelow(l, t);
}
// </vc-code>
