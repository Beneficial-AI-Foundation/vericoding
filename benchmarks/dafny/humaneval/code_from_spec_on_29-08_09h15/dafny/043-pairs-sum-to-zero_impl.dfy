

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: def pairs_sum_to_zero(numbers: List[int]) -> Bool
pairs_sum_to_zero takes a list of integers as an input. it returns True if there are two distinct elements in the list that sum to zero, and False otherwise.
*/
// </vc-description>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)
   // post-conditions-start
    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
  result := false;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant !result ==> forall x : int, y : int :: 0 <= x < i && 0 <= y < |l| && x != y ==> l[x] + l[y] != 0
    invariant result ==> exists x : int, y : int :: 0 <= x < |l| && 0 <= y < |l| && x != y && l[x] + l[y] == 0
  {
    var j := 0;
    while j < |l|
      invariant 0 <= j <= |l|
      invariant !result ==> forall y : int :: 0 <= y < j && i != y ==> l[i] + l[y] != 0
      invariant result ==> exists x : int, y : int :: 0 <= x < |l| && 0 <= y < |l| && x != y && l[x] + l[y] == 0
    {
      if i != j && l[i] + l[j] == 0 {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

