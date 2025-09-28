// <vc-preamble>

predicate HasTripleSumToZero(l: seq<int>)
{
    exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>
predicate exists_i_j_k(l: seq<int>, i: int, j: int, k: int) { 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0 }
// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasTripleSumToZero(l)
// </vc-spec>
// <vc-code>
{
    var n := |l|;
    result := false;
    if n < 3 {
        return;
    }
    var i := 0;
    while i < n - 2
        invariant 0 <= i <= n - 2
        invariant result == (exists i_0, j_0, k_0 :: 0 <= i_0 < j_0 < k_0 < n && i_0 < i && l[i_0] + l[j_0] + l[k_0] == 0)
    {
        var j := i + 1;
        while j < n - 1
            invariant i + 1 <= j <= n - 1
            invariant result == (exists i_0, j_0, k_0 :: 0 <= i_0 < j_0 < k_0 < n && (i_0 < i || (i_0 == i && j_0 < j)) && l[i_0] + l[j_0] + l[k_0] == 0)
        {
            var k := j + 1;
            while k < n
                invariant j + 1 <= k <= n
                invariant result == (exists i_0, j_0, k_0 :: 0 <= i_0 < j_0 < k_0 < n && (i_0 < i || (i_0 == i && j_0 < j) || (i_0 == i && j_0 == j && k_0 < k)) && l[i_0] + l[j_0] + l[k_0] == 0)
            {
                if l[i] + l[j] + l[k] == 0 {
                    result := true;
                    return;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    return;
}
// </vc-code>
