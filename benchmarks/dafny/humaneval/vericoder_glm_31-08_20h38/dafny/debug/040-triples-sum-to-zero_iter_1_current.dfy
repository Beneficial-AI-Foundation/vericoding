

// <vc-helpers>

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
  var n := |l|;
  for i := 0 to n-1
    for j := 0 to n-1
      if j != i {
        for k := 0 to n-1
          if k != i && k != j {
            if l[i] + l[j] + l[k] == 0 {
              return true;
            }
          }
      }
  return false;
}
// </vc-code>

