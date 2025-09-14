// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)

    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
// </vc-spec>
// <vc-code>
{
  b := true;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant b == (forall k :: 0 <= k < i ==> l[k] < t)
  {
    if l[i] >= t {
      b := false;
    }
    i := i + 1;
  }
}
// </vc-code>
