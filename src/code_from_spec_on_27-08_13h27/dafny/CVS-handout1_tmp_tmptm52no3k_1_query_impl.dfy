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
lemma SumProperty(a: array<int>, i: int, j: int, k: int)
    requires 0 <= i <= k <= j <= a.Length
    ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
    decreases j - i
{
    if (i == j) {
        assert sum(a, i, j) == 0;
        assert sum(a, i, k) == 0;
        assert sum(a, k, j) == 0;
    } else if (i == k) {
        assert sum(a, i, k) == 0;
        assert sum(a, i, j) == sum(a, k, j);
    } else if (k == j) {
        assert sum(a, k, j) == 0;
        assert sum(a, i, j) == sum(a, i, k);
    } else {
        calc {
            sum(a, i, j);
            a[i] + sum(a, i+1, j);
            { SumProperty(a, i+1, j, k); }
            a[i] + sum(a, i+1, k) + sum(a, k, j);
            { assert sum(a, i, k) == a[i] + sum(a, i+1, k); }
            sum(a, i, k) + sum(a, k, j);
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method query(a: array<int>, i: int, j: int) returns (res:int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
// </vc-spec>
// </vc-spec>

// <vc-code>
method Query(a: array<int>, i: int, j: int) returns (res: int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
{
    res := 0;
    var k := i;
    while k < j
        invariant i <= k <= j
        invariant res == sum(a, i, k)
        decreases j - k
    {
        res := res + a[k];
        k := k + 1;
        assert res == sum(a, i, k);
    }
}
// </vc-code>
