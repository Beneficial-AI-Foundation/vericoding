

// <vc-helpers>
function method SumExists(l: seq<int>, i: int, j: int, k: int) : bool
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

  for i := 0 to |l| - 1
    ensures forall x, y, z :: 0 <= x < i && 0 <= y < |l| && 0 <= z < |l| && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
  {
    for j := 0 to |l| - 1
      ensures forall x :: 0 <= x <= i && forall y, z :: 0 <= y < j && 0 <= z < |l| && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
    {
      for k := 0 to |l| - 1
        ensures forall x :: 0 <= x <= i && forall y :: 0 <= y <= j && forall z :: 0 <= z < k && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
        ensures (exists a, b, c :: 0 <= a < |l| && 0 <= b < |l| && 0 <= c < |l| && a != b && b != c && a != c && l[a] + l[b] + l[c] == 0) ==>
                (exists a, b, c :: 0 <= a <= i && 0 <= b <= j && 0 <= c < k && a != b && b != c && a != c && l[a] + l[b] + l[c] == 0) ||
                (exists a, b, c :: 0 <= a <= i && 0 <= b <= j && 0 <= c < |l| && a != b && b != c && a != c && l[a] + l[b] + l[c] == 0 && (a > i || b > j || c >= k))
      {
        if i != j && j != k && i != k && l[i] + l[j] + l[k] == 0 then
          return true;
      }
    }
  }
  return false;
}
// </vc-code>

