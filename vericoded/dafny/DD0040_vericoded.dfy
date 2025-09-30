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
lemma sum_lemma(a: array<int>, i: int, j: int, k: int)
    requires 0 <= i <= k <= j <= a.Length
    ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
    decreases j - i
{
    if i == k {
        assert sum(a, i, k) == 0;
    } else {
        sum_lemma(a, i+1, j, k);
    }
}

lemma sum_extend(a: array<int>, i: int, j: int)
    requires 0 <= i <= j < a.Length
    ensures sum(a, i, j) + a[j] == sum(a, i, j+1)
    decreases j - i
{
    if i == j {
        assert sum(a, i, j) == 0;
        assert sum(a, i, j+1) == a[i] + sum(a, i+1, j+1) == a[i] + 0 == a[i];
    } else {
        assert sum(a, i, j+1) == a[i] + sum(a, i+1, j+1);
        sum_extend(a, i+1, j);
        assert sum(a, i+1, j) + a[j] == sum(a, i+1, j+1);
        assert sum(a, i, j) == a[i] + sum(a, i+1, j);
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
    var s := 0;
    var idx := i;
    
    while idx < j
        invariant i <= idx <= j
        invariant s == sum(a, i, idx)
    {
        s := s + a[idx];
        sum_extend(a, i, idx);
        idx := idx + 1;
    }
    
    res := s;
}
// </vc-code>

