predicate ValidInput(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>)
{
    n > 0 && m >= 0 && |A| == n && |queries| == m &&
    forall q :: q in queries ==> 1 <= q.0 <= q.1 <= n
}

predicate ValidResult(A: seq<int>, queries: seq<(int, int, int)>, result: seq<int>)
{
    |result| == |queries| &&
    forall i :: 0 <= i < |queries| ==> (
        var l, r, x := queries[i].0, queries[i].1, queries[i].2;
        (result[i] == -1 ==> (forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
        (result[i] != -1 ==> l <= result[i] <= r && 0 <= result[i]-1 < |A| && A[result[i]-1] != x)
    )
}

// <vc-helpers>
/**
 * Finds the index of the first element in a subsequence of A that is NOT equal to x.
 *
 * @param A The input sequence of integers.
 * @param l The starting index (1-based) of the subsequence to search within.
 * @param r The ending index (1-based) of the subsequence to search within.
 * @param x The value to compare against.
 * @return The 1-based index of the first element in A[l..r] that is not equal to x,
 *         or -1 if all elements in A[l..r] are equal to x.
 */
function find_first_different(A: seq<int>, l: int, r: int, x: int): (idx: int)
    requires 1 <= l <= r
    requires 0 <= l-1 < |A| && 0 <= r-1 < |A|
    ensures (idx == -1 ==> (forall k :: l <= k <= r ==> A[k-1] == x))
    ensures (idx != -1 ==> l <= idx <= r && A[idx-1] != x)
    ensures (idx != -1 ==> (forall k :: l <= k < idx ==> A[k-1] == x))
{
    var i := l;
    while i <= r
        invariant l <= i <= r + 1
        invariant forall k :: l <= k < i ==> A[k-1] == x
    {
        if A[i-1] != x {
            return i;
        }
        i := i + 1;
    }
    return -1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures ValidResult(A, queries, result)
// </vc-spec>
// <vc-code>
{
    var result_seq: seq<int> := [];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |result_seq| == i
        invariant forall k :: 0 <= k < i ==> (
            var l_k, r_k, x_k := queries[k].0, queries[k].1, queries[k].2;
            var current_res := result_seq[k];
            (current_res == -1 ==> (forall j :: l_k <= j <= r_k ==> A[j-1] == x_k)) &&
            (current_res != -1 ==> l_k <= current_res <= r_k && A[current_res-1] != x_k)
        )
    {
        var l, r, x := queries[i].0, queries[i].1, queries[i].2;
        var first_diff_idx := find_first_different(A, l, r, x);
        result_seq := result_seq + [first_diff_idx];
        i := i + 1;
    }
    return result_seq;
}
// </vc-code>

