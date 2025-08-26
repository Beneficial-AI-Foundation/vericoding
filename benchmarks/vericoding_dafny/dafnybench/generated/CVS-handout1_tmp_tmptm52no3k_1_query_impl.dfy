/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

// <vc-spec>
function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
    decreases j - i
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}



//(b)

// <vc-helpers>
lemma sum_step(a: array<int>, i: int, j: int)
    requires 0 <= i < j <= a.Length
    ensures sum(a, i, j) == sum(a, i, j-1) + a[j-1]
    decreases j - i
{
    if i == j-1 {
        assert sum(a, i, j-1) == 0;
        assert sum(a, i, j) == a[i];
        assert a[j-1] == a[i];
    } else {
        sum_step(a, i+1, j);
        assert sum(a, i+1, j) == sum(a, i+1, j-1) + a[j-1];
        assert sum(a, i, j) == a[i] + sum(a, i+1, j);
        assert sum(a, i, j-1) == a[i] + sum(a, i+1, j-1);
    }
}
// </vc-helpers>

method query(a: array<int>, i: int, j: int) returns (res:int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
  res := 0;
  var k := i;
  while k < j
    invariant i <= k <= j
    invariant res == sum(a, i, k)
  {
    sum_step(a, i, k+1);
    res := res + a[k];
    k := k + 1;
  }
}
// </vc-code>

//(c)

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    reads c, a
{
    forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}

lemma aux(a: array<int>, c: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    decreases j - i
    ensures forall k: int :: i <= k <= j ==> sum(a, i, k) + sum(a, k, j) == c[k] - c[i] + c[j] - c[k] //sum(a, i, j) == c[j] - c[i]
{}