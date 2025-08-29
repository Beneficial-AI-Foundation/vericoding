

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: def below_threshold(numbers: List[Int], threshold: Int) -> bool
*/
// </vc-description>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)
    // post-conditions-start
    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall j :: 0 <= j < i ==> l[j] < t
  {
    if l[i] >= t {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

