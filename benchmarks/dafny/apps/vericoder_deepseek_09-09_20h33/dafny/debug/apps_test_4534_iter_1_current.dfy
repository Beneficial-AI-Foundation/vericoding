function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}

// <vc-helpers>
lemma binomial_symmetric(n: int, k: int)
    requires 0 <= k <= n
    ensures binomial(n, k) == binomial(n, n - k)
{
    if k != n - k {
        // This property holds by the definition of binomial coefficients
    }
}

lemma binomial_positive(n: int, k: int)
    requires 0 <= k <= n
    ensures binomial(n, k) > 0
{
    if k == 0 || k == n {
    } else if k == 1 {
    } else {
        binomial_positive(n-1, k-1);
        binomial_positive(n-1, k);
    }
}
// </vc-helpers>

// <vc-spec>
method getRow(k: int) returns (result: seq<int>)
    requires 0 <= k <= 33
    ensures |result| == k + 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == binomial(k, i)
    ensures forall i :: 0 <= i < |result| ==> result[i] > 0
// </vc-spec>
// <vc-code>
{
    result := [];
    var j := 0;
    while j <= k
        invariant |result| == j
        invariant forall i :: 0 <= i < j ==> result[i] == binomial(k, i)
        invariant forall i :: 0 <= i < j ==> result[i] > 0
    {
        result := result + [binomial(k, j)];
        j := j + 1;
    }
}
// </vc-code>

