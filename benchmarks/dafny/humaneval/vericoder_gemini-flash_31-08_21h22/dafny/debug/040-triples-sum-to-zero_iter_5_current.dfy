

// <vc-helpers>
function IsDistinct(a: int, b: int, c: int): bool
{
  a != b && b != c && a != c
}
// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l : seq<int>) returns (result : bool)
    // post-conditions-start
    ensures result ==> exists i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    ensures !result ==> forall i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |l|; // Corrected: Use |l| for sequence length
  if n < 3 {
    return false;
  }

  for i := 0 to n - 1 {
    for j := 0 to n - 1 {
      for k := 0 to n - 1 {
        if i != j && j != k && i != k && l[i] + l[j] + l[k] == 0 {
          return true;
        }
      }
    }
  }
  return false;
}
// </vc-code>

