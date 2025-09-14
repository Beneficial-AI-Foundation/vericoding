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
lemma sum_split(a: array<int>, i: int, k: int, j: int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
  decreases j - k
{
  if k == j {
    assert sum(a, k, j) == 0;
    assert sum(a, i, j) == sum(a, i, k);
  } else {
    calc {
      sum(a, i, j);
      a[j-1] + sum(a, i, j-1);
      { reveal sum(); }
      a[j-1] + (sum(a, i, k) + sum(a, k, j-1));
      { sum_split(a, i, k, j-1); }
      sum(a, i, k) + (a[j-1] + sum(a, k, j-1));
      sum(a, i, k) + sum(a, k, j);
      { reveal sum(); }
    }
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
  r := c[j] - c[i];
  assert sum(a, 0, j) == c[j];
  assert sum(a, 0, i) == c[i];
  sum_split(a, 0, i, j);
  assert sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j);
}
// </vc-code>

