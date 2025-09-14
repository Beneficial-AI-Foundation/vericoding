// <vc-preamble>
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
  decreases j
{
  if i == j then 0
  else a[j-1] + sum(a, i, j-1)
}

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  reads c, a
{
  a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed reads clause and added proof body */
lemma sum_split(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= a.Length
  ensures sum(a, i, k) == sum(a, i, j) + sum(a, j, k)
  decreases k - j
{
  if j < k {
    sum_split(a, i, j, k - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c)
  ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use helper lemma to prove the correctness of prefix sum subtraction */
  sum_split(a, 0, i, j);
  r := c[j] - c[i];
}
// </vc-code>
