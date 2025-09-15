// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate HasPairSumToZero(l: seq<int>) {
  exists i: int, j: int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
}

lemma PairSumCorrectness(l: seq<int>, found: bool, witness_i: int, witness_j: int)
  requires found ==> (0 <= witness_i < |l| && 0 <= witness_j < |l| && witness_i != witness_j && l[witness_i] + l[witness_j] == 0)
  requires !found ==> (forall i: int, j: int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0)
  ensures found == HasPairSumToZero(l)
{}
// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)

    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall x: int, y: int :: 0 <= x < i && 0 <= y < |l| && x != y ==> l[x] + l[y] != 0
  {
    var j := 0;
    while j < |l|
      invariant 0 <= j <= |l|
      invariant forall y: int :: 0 <= y < j && i != y ==> l[i] + l[y] != 0
    {
      if i != j && l[i] + l[j] == 0 {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
