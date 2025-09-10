function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}

// <vc-helpers>
function old_binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else old_binomial(n-1, k-1) + old_binomial(n-1, k)
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
    if k == 0 {
        return [1];
    } else {
        var prevRow := getRow(k - 1);
        var result_seq: seq<int> := [1];
        var i := 1;
        while i < k
            invariant 0 < i <= k
            invariant |result_seq| == i
            invariant forall j :: 0 <= j < |result_seq| ==> result_seq[j] == binomial(k, j)
            invariant forall j :: 0 <= j < |result_seq| ==> result_seq[j] > 0
            invariant |prevRow| == k
            invariant forall j :: 0 <= j < |prevRow| ==> prevRow[j] == binomial(k - 1, j)
        {
            result_seq := result_seq + [prevRow[i - 1] + prevRow[i]];
            i := i + 1;
        }
        result_seq := result_seq + [1];
        return result_seq;
    }
}
// </vc-code>

