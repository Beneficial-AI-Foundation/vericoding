

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
  if |l| < 2 {
    return false;
  }
  for i := 0 to |l| - 1
  {
    for j := i + 1 to |l| - 1
    {
      if l[i] + l[j] == 0 {
        return true;
      }
    }
  }
  return false;
}
// </vc-code>

