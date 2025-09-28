// <vc-preamble>

predicate BelowThreshold(l: seq<int>, t: int)
{
    forall i :: 0 <= i < |l| ==> l[i] < t
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CheckBelowThreshold(l: seq<int>, t: int) returns (result: bool)
    ensures result == BelowThreshold(l, t)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall k :: 0 <= k < i ==> l[k] < t
  {
    if l[i] >= t {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
