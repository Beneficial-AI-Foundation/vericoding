function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}

// <vc-helpers>
lemma BinomialPositive(n: int, k: int)
    requires 0 <= k <= n
    ensures binomial(n, k) > 0
    decreases n
{
    if k > 0 && k < n && k != 1 {
        BinomialPositive(n-1, k-1);
        BinomialPositive(n-1, k);
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
    var res := new int[k + 1];
    var i := 0;
    while i <= k
        invariant 0 <= i <= k + 1
        invariant forall j :: 0 <= j < i ==> res[j] == binomial(k, j)
        invariant forall j :: 0 <= j < i ==> res[j] > 0
    {
        res[i] := binomial(k, i);
        BinomialPositive(k, i);
        i := i + 1;
    }
    result := res[..];
}
// </vc-code>

