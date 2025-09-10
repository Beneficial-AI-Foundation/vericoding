function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}

// <vc-helpers>
lemma binomial_positive(n: int, k: int)
    requires 0 <= k <= n
    ensures binomial(n, k) > 0
{
    if k == 0 || k == n {
        assert binomial(n, k) == 1;
    } else if k == 1 {
        assert binomial(n, k) == n;
        assert n > 0;
    } else {
        binomial_positive(n-1, k-1);
        binomial_positive(n-1, k);
        assert binomial(n, k) == binomial(n-1, k-1) + binomial(n-1, k);
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
    var i := 0;
    while i <= k
        invariant 0 <= i <= k + 1
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == binomial(k, j)
        invariant forall j :: 0 <= j < i ==> result[j] > 0
    {
        var binom_val := binomial(k, i);
        binomial_positive(k, i);
        result := result + [binom_val];
        i := i + 1;
    }
}
// </vc-code>

