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
lemma lemma_sum_step(a: array<int>, i: int, j: int)
requires 0 <= i < j <= a.Length
decreases j - i
ensures sum(a, i, j) == sum(a, i, j-1) + a[j-1]
{
  if j == i + 1 {
    calc == {
             sum(a, i, j);
             { assert sum(a, i, j) == a[i]; }
             a[i];
             ==
             sum(a, i, j-1) + a[j-1];
             { assert sum(a, i, j-1) == sum(a, i, i) == 0; assert a[j-1] == a[i]; }
             0 + a[i];
           }
  } else {
    lemma_sum_step(a, i+1, j);
    calc == {
             sum(a, i, j);
             { assert sum(a, i, j) == a[i] + sum(a, i+1, j); }
             a[i] + sum(a, i+1, j);
             == { lemma_sum_step(a, i+1, j); }
             a[i] + (sum(a, i+1, j-1) + a[j-1]);
             ==
             (a[i] + sum(a, i+1, j-1)) + a[j-1];
             { assert a[i] + sum(a, i+1, j-1) == sum(a, i, j-1); }
             sum(a, i, j-1) + a[j-1];
           }
  }
}
// </vc-helpers>

// <vc-spec>
method query(a: array<int>, i: int, j: int) returns (res:int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
  res := 0;
  var k := i;
  while k < j
    invariant 0 <= k <= j <= a.Length
    invariant res == sum(a, i, k)
  {
    res := res + a[k];
    k := k + 1;
    lemma_sum_step(a, i, k);
  }
}
// </vc-code>

