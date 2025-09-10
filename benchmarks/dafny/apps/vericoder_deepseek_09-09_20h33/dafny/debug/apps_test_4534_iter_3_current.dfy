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
    if k == 0 || k == n {
        // Base cases
    } else if k == 1 {
        // n - k = n - 1, and binomial(n,1) = n = binomial(n, n-1)
    } else {
        binomial_symmetric(n-1, k-1);
        binomial_symmetric(n-1, k);
        // binomial(n, k) = binomial(n-1, k-1) + binomial(n-1, k)
        // binomial(n, n-k) = binomial(n-1, n-k-1) + binomial(n-1, n-k)
        // Note that binomial(n-1, n-k-1) = binomial(n-1, k) by symmetric property
        // and binomial(n-1, n-k) = binomial(n-1, k-1) by symmetric property
        // So both sides are equal
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
    assert j == k + 1;
}
// </vc-code>

