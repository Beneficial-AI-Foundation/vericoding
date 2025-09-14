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
lemma sum_and_prefix_sum(a: array<int>, c: array<int>, i: int, j: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a, c)
    ensures sum(a, i, j) == c[j] - c[i]
    decreases j - i
{
    if i == j {
        // sum(a, i, i) == 0
        // c[i] - c[i] == 0
    } else {
        // sum(a, i, j) == a[i] + sum(a, i+1, j)
        // c[j] - c[i] == c[j] - (c[i+1] - a[i]) == (c[j] - c[i+1]) + a[i]
        calc {
            sum(a, i, j);
            a[i] + sum(a, i + 1, j);
            {
                assert is_prefix_sum_for(a, c) by {
                    assert forall k :: 0 <= k < a.Length ==> c[k+1] == c[k] + a[k];
                }
                assert c[i+1] == c[i] + a[i]; // This is by is_prefix_sum_for(a,c) and 0 <= i < a.Length
                sum_and_prefix_sum(a, c, i+1, j);
            }
            a[i] + (c[j] - c[i+1]);
            (c[i+1] - c[i]) + (c[j] - c[i+1]);
            c[j] - c[i];
        }
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
    r := c[j] - c[i];
    sum_and_prefix_sum(a, c, i, j);
}
// </vc-code>

