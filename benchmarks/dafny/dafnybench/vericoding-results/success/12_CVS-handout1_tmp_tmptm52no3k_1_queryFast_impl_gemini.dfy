// <vc-preamble>
function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
    decreases j - i
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    reads c, a
{
    forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}
// </vc-preamble>

// <vc-helpers>
lemma SumFromPrefixIsDifference(a: array<int>, c: array<int>, i: int, j: int)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    requires 0 <= i <= j <= a.Length
    ensures sum(a, i, j) == c[j] - c[i]
    decreases j - i
{
    if i < j {
        SumFromPrefixIsDifference(a, c, i + 1, j);
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
  SumFromPrefixIsDifference(a, c, i, j);
  r := c[j] - c[i];
}
// </vc-code>
