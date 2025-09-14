// 1 a)

// [ai, aj[
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
  decreases j
{
  if i == j then 0
  else a[j-1] + sum(a, i, j-1)
}

// 1 b)

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  reads c, a
{
  a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}

// <vc-helpers>
lemma sum_lemma(a: array<int>, i: int, k: int, j: int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
  decreases j - k
{
  if k < j {
    sum_lemma(a, i, k, j-1);
  }
}

lemma sum_decomposition(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i)
{
  sum_lemma(a, 0, i, j);
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
  r := c[j] - c[i];
  sum_decomposition(a, i, j);
}
// </vc-code>

