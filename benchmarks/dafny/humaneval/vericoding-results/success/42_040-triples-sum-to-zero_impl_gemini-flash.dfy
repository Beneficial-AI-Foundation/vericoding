// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l : seq<int>) returns (result : bool)

    ensures result ==> exists i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    ensures !result ==> forall i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
// </vc-spec>
// <vc-code>
{
  var n := |l|;
  if n < 3 {
    return false;
  }

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall x: int, y: int, z: int :: 0 <= x < i && 0 <= y < n && 0 <= z < n && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
  {
    var j := i + 1;
    while j < n
      invariant i < j <= n
      invariant forall x: int, y: int, z: int :: 0 <= x < i && 0 <= y < n && 0 <= z < n && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
      invariant forall y: int, z: int :: i < y < j && 0 <= z < n && i != y && y != z && i != z ==> l[i] + l[y] + l[z] != 0
    {
      var k := j + 1;
      while k < n
        invariant j < k <= n
        invariant forall x: int, y: int, z: int :: 0 <= x < i && 0 <= y < n && 0 <= z < n && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
        invariant forall y: int, z: int :: i < y < j && 0 <= z < n && i != y && y != z && i != z ==> l[i] + l[y] + l[z] != 0
        invariant forall z: int :: j < z < k && i != j && j != z && i != z ==> l[i] + l[j] + l[z] != 0
      {
        if l[i] + l[j] + l[k] == 0 {
          return true;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
