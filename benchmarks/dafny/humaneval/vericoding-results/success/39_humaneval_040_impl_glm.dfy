// <vc-preamble>

predicate HasTripleSumToZero(l: seq<int>)
{
    exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasTripleSumToZero(l)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): replaced triple loop with quantifier */
{
  result := exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0;
}
// </vc-code>
