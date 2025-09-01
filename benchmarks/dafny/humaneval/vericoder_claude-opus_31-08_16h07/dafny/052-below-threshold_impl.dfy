

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)
    // post-conditions-start
    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  b := true;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant b == (forall j : int :: 0 <= j < i ==> l[j] < t)
  {
    if l[i] >= t {
      b := false;
    }
    i := i + 1;
  }
}
// </vc-code>

