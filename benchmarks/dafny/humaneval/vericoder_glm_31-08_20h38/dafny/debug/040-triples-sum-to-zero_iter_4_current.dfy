

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
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
  for o := 0 to n
  {
    for p := o + 1 to n
    {
      for q := p + 1 to n
      {
        if l[o] + l[p] + l[q] == 0
        {
          return true;
        }
      }
    }
  }
  return false;
}
// </vc-code>

