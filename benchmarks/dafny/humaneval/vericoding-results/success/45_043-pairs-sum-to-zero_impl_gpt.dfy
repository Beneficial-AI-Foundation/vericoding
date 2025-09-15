// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate PairSumZeroExists(l: seq<int>) {
  exists i:int, j:int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
}
// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)

    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
// </vc-spec>
// <vc-code>
{
  result := exists i:int, j:int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0;
}
// </vc-code>
