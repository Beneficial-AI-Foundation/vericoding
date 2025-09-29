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
lemma sum_split(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= a.Length
  ensures sum(a, i, k) == sum(a, i, j) + sum(a, j, k)
  decreases k - j
{
  if j == k {
    assert sum(a, j, k) == 0;
  } else {
    sum_split(a, i, j, k-1);
    assert sum(a, i, k) == sum(a, i, k-1) + a[k-1];
    assert sum(a, i, k-1) == sum(a, i, j) + sum(a, j, k-1);
    assert sum(a, j, k) == sum(a, j, k-1) + a[k-1];
  }
}

lemma sum_difference(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i)
{
  sum_split(a, 0, i, j);
  assert sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j);
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
  sum_difference(a, i, j);
  r := c[j] - c[i];
}
// </vc-code>

