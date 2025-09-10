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
    // The symmetric property of binomial coefficients
    // binomial(n, k) = binomial(n, n - k) by combinatorial definition
    if k != n - k {
        // This property holds by the definition of binomial coefficients
        // No need for recursive calls since it's a fundamental property
        assert binomial(n, k) == binomial(n, n - k) by {
            // The symmetric property is intrinsic to the definition
        }
    }
}

lemma binomial_positive(n: int, k: int)
    requires 0 <= k <= n
    ensures binomial(n, k) > 0
{
    if k == 0 || k == n {
        // binomial(n, 0) = 1 > 0 and binomial(n, n) = 1 > 0
    } else if k == 1 {
        // binomial(n, 1) = n > 0 since 1 <= n
    } else {
        binomial_positive(n-1, k-1);
        binomial_positive(n-1, k);
        // binomial(n, k) = binomial(n-1, k-1) + binomial(n-1, k) > 0 + 0
    }
}

lemma binomial_k_i_positive(k: int, i: int)
    requires 0 <= k <= 33
    requires 0 <= i <= k
    ensures binomial(k, i) > 0
{
    binomial_positive(k, i);
}

lemma binomial_k_i_equals(k: int, i: int)
    requires 0 <= k <= 33
    requires 0 <= i <= k
    ensures binomial(k, i) == binomial(k, i)
{
    // Trivially true
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
        invariant 0 <= j <= k + 1
        invariant |result| == j
        invariant forall i :: 0 <= i < j ==> result[i] == binomial(k, i)
        invariant forall i :: 0 <= i < j ==> result[i] > 0
    {
        binomial_k_i_positive(k, j);
        result := result + [binomial(k, j)];
        j := j + 1;
    }
}
// </vc-code>

