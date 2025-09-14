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
lemma SumEqualsC(a: array<int>, c: array<int>, i: int, j: int)
  requires is_prefix_sum_for(a,c)
  requires 0 <= i <= j <= a.Length
  ensures sum(a,i,j) == c[j] - c[i]
  decreases j - i
{
  if j == i {
    // sum(a,i,i) == 0 and c[i]-c[i] == 0
  } else {
    assert j > 0;
    assert c[j] == sum(a,0,j);
    assert c[j-1] == sum(a,0,j-1);
    assert sum(a,0,j) == a[j-1] + sum(a,0,j-1);
    assert c[j] - c[j-1] == a[j-1];
    SumEqualsC(a,c,i,j-1);
    assert sum(a,i,j) == a[j-1] + sum(a,i,j-1);
    assert sum(a,i,j-1) == c[j-1] - c[i];
    assert sum(a,i,j) == c[j] - c[i];
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
  SumEqualsC(a, c, i, j);
  r := c[j] - c[i];
}
// </vc-code>

