

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)
   // post-conditions-start
    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant !exists x, y : int :: 0 <= x < i && x < y < i && l[x] + l[y] == 0
  {
    var j := i + 1;
    while j < |l|
        invariant i < j <= |l|
        invariant !exists m : int :: i < m < j && l[i] + l[m] == 0
    {
      if l[i] + l[j] == 0 {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

