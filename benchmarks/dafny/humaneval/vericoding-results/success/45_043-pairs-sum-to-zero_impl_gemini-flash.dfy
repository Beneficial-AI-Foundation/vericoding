// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)

    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall x : int, y : int :: 0 <= x < i && 0 <= y < |l| && x != y ==> l[x] + l[y] != 0
  {
    var j := 0;
    while j < |l|
      invariant 0 <= i < |l|
      invariant 0 <= j <= |l|
      invariant forall x : int, y : int :: 0 <= x < i && 0 <= y < |l| && x != y ==> l[x] + l[y] != 0
      invariant forall y : int :: 0 <= y < j && i != y ==> l[i] + l[y] != 0
    {
      if i != j && l[i] + l[j] == 0 {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
