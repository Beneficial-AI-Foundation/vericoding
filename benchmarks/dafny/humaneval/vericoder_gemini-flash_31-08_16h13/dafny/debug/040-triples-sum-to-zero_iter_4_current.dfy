

// <vc-helpers>
function SumExists(l: seq<int>, i: int, j: int, k: int) : bool
  reads l
  requires 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k
{
  l[i] + l[j] + l[k] == 0
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
  if |l| < 3 then
    return false;

  for i := 0 to |l| - 1 {
    for j := 0 to |l| - 1 {
      for k := 0 to |l| - 1 {
        if i != j && j != k && i != k && l[i] + l[j] + l[k] == 0 then
          return true;
      }
    }
  }
  return false;
}
// </vc-code>

