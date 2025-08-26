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

// <vc-helpers>
lemma sum_prefix_relation(a: array<int>, c: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    decreases j - i
    ensures sum(a, i, j) == c[j] - c[i]
{
    if i == j {
        // Base case: sum(a, i, i) == 0 and c[i] - c[i] == 0
    } else {
        // Inductive case
        sum_prefix_relation(a, c, i+1, j);
        // sum(a, i, j) = a[i] + sum(a, i+1, j)
        //              = a[i] + (c[j] - c[i+1])    [by inductive hypothesis]
        //              = a[i] + c[j] - c[i+1]
        //              = c[j] - (c[i+1] - a[i])
        //              = c[j] - c[i]               [since c[i+1] = c[i] + a[i]]
    }
}
// </vc-helpers>

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a,c)  
    ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
    sum_prefix_relation(a, c, i, j);
    r := c[j] - c[i];
}
// </vc-code>