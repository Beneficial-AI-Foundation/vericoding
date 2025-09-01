

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

lemma index_bounds_lemma(i: int, n: int)
  requires 0 <= i <= n
  ensures forall j :: 0 <= j < i ==> j < n
{
}
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
  if |l| < 3 {
    return false;
  }
  
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall x, y, z :: 0 <= x < i && 0 <= y < |l| && 0 <= z < |l| && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
  {
    var j := i + 1;
    while j < |l|
      invariant i < j <= |l|
      invariant forall x, y, z :: 0 <= x < i && 0 <= y < |l| && 0 <= z < |l| && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
      invariant forall y, z :: i <= y < j && 0 <= z < |l| && y != z && i != z && i != y ==> l[i] + l[y] + l[z] != 0
    {
      var k := j + 1;
      while k < |l|
        invariant j < k <= |l|
        invariant forall z :: j <= z < k && z != i && z != j ==> l[i] + l[j] + l[z] != 0
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

