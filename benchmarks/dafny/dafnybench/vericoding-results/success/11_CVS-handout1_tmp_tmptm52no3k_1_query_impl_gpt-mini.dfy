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
lemma SumCons(a: array<int>, i: int, k: int)
    requires 0 <= i <= k < a.Length
    ensures sum(a, i, k+1) == sum(a, i, k) + a[k]
    decreases k - i
{
    if i == k {
        // sum(a,i,k) == sum(a,k,k) == 0
        // sum(a,i,k+1) == sum(a,k,k+1) == a[k]
        assert sum(a, i, k) == 0;
        assert sum(a, i, k+1) == a[k];
    } else {
        // unfold definitions
        assert sum(a, i, k) == a[i] + sum(a, i+1, k);
        assert sum(a, i, k+1) == a[i] + sum(a, i+1, k+1);
        // apply induction on (i+1, k)
        SumCons(a, i+1, k);
        assert sum(a, i+1, k+1) == sum(a, i+1, k) + a[k];
        // conclude
        assert sum(a, i, k+1) == a[i] + (sum(a, i+1, k) + a[k]);
        assert sum(a, i, k+1) == (a[i] + sum(a, i+1, k)) + a[k];
        assert sum(a, i, k+1) == sum(a, i, k) + a[k];
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
  var k := i;
  var acc := 0;
  while k < j
    invariant i <= k <= j
    invariant acc == sum(a, i, k)
    decreases j - k
  {
    // use lemma to relate sum(a,i,k+1) with sum(a,i,k) + a[k]
    SumCons(a, i, k);
    acc := acc + a[k];
    k := k + 1;
  }
  return acc;
}
// </vc-code>

