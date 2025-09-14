/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
    decreases j - i
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}



//(b)

//(c)

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    reads c, a
{
    forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method query(a: array<int>, i: int, j: int) returns (res:int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
  var k := j;
  res := 0;
  assert sum(a, j, j) == 0;
  while i < k
    invariant 0 <= i <= k <= j <= a.Length
    invariant res == sum(a, k, j)
    decreases k - i
  {
    k := k - 1;
    assert 0 <= k < j <= a.Length;
    assert sum(a, k, j) == a[k] + sum(a, k + 1, j);
    res := res + a[k];
    assert res == sum(a, k, j);
  }
}
// </vc-code>

