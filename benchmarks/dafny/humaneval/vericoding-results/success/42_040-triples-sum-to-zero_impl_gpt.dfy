// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate Distinct3(i: int, j: int, k: int) { i != j && j != k && i != k }
function Sum3(l: seq<int>, i: int, j: int, k: int): int
  requires 0 <= i < |l|
  requires 0 <= j < |l|
  requires 0 <= k < |l|
{
  l[i] + l[j] + l[k]
}
// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l : seq<int>) returns (result : bool)

    ensures result ==> exists i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    ensures !result ==> forall i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
// </vc-spec>
// <vc-code>
{
  result := exists i:int, j:int, k:int ::
    0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| &&
    i != j && j != k && i != k && l[i] + l[j] + l[k] == 0;
}
// </vc-code>
