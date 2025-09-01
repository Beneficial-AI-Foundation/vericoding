

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
  var index := 0;
  while index < |l|
    invariant index >= 0
    invariant forall j: int :: 0 <= j && j < index ==> l[j] < t
  {
    if l[index] >= t {
      b := false;
      return;
    }
    index := index + 1;
  }
  b := true;
}
// </vc-code>

