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
    if i < k {
        sum_lemma(a, i+1, j, k);
        assert sum(a, i, j) == a[i] + sum(a, i+1, j);
        assert sum(a, i, k) == a[i] + sum(a, i+1, k);
        assert sum(a, i, k) + sum(a, k, j) == (a[i] + sum(a, i+1, k)) + sum(a, k, j);
        assert a[i] + (sum(a, i+1, k) + sum(a, k, j)) == a[i] + sum(a, i+1, j);
    }
}

lemma prefix_sum_property(a: array<int>, c: array<int>, i: int, j: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires is_prefix_sum_for(a, c)
    requires 0 <= i <= j <= a.Length
    ensures c[j] - c[i] == sum(a, i, j)
    decreases j - i
{
    if i < j {
        prefix_sum_property(a, c, i, j-1);
        assert c[j-1] - c[i] == sum(a, i, j-1);
        calc {
            c[j] - c[i];
            ==
            (c[j-1] + a[j-1]) - c[i];
            ==
            (c[j-1] - c[i]) + a[j-1];
            ==
            sum(a, i, j-1) + a[j-1];
            ==
            sum(a, i, j);
        }
    } else {
        assert i == j;
        assert c[j] - c[i] == 0;
    }
}
// </vc-helpers>

// <vc-spec>
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a,c)  
    ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
  prefix_sum_property(a, c, i, j);
  r := c[j] - c[i];
}
// </vc-code>

