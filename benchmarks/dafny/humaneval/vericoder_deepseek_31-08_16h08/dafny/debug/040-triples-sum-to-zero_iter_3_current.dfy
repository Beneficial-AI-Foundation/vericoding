

// <vc-helpers>
predicate triple_exists(l: seq<int>)
{
  exists i, j, k :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
}

predicate no_triple_exists(l: seq<int>)
{
  forall i, j, k :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
}

lemma triple_exists_equivalence(l: seq<int>)
  ensures triple_exists(l) <==> exists i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
{
}

lemma no_triple_exists_equivalence(l: seq<int>)
  ensures no_triple_exists(l) <==> forall i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
{
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
  if |l| < 3 {
    return false;
  }
  
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall x, y, z :: 0 <= x < i && 0 <= y < |l| && 0 <= z < |l| && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
  {
    var j := 0;
    while j < |l|
      invariant 0 <= j <= |l|
      invariant forall z :: 0 <= z < |l| && z != i && z != j && i != j ==> l[i] + l[j] + l[z] != 0
      invariant forall x, y, z :: 0 <= x < i && 0 <= y < |l| && 0 <= z < |l| && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
      invariant forall x, y, z :: 0 <= x < i && 0 <= y < j && 0 <= z < |l| && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
    {
      if j != i {
        var k := 0;
        while k < |l|
          invariant 0 <= k <= |l|
          invariant forall z :: 0 <= z < k && z != i && z != j ==> l[i] + l[j] + l[z] != 0
        {
          if k != i && k != j {
            if l[i] + l[j] + l[k] == 0 {
              return true;
            }
          }
          k := k + 1;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

