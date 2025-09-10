predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 &&
    |a| == n &&
    (forall i :: 0 <= i < n ==> 1 <= a[i] <= n) &&
    (forall i, j :: 0 <= i < j < n ==> a[i] != a[j])
}

predicate ValidOutput(n: int, result: int)
{
    0 <= result <= n
}

function ReversedArray(a: seq<int>): seq<int>
    requires |a| >= 1
    ensures |ReversedArray(a)| == |a|
{
    seq(|a|, i requires 0 <= i < |a| => a[|a|-1-i])
}

predicate HasIncreasingPair(ar: seq<int>)
{
    exists i :: 1 <= i < |ar| && ar[i] > ar[i-1]
}

function CorrectResult(n: int, a: seq<int>): int
    requires ValidInput(n, a)
    ensures ValidOutput(n, CorrectResult(n, a))
{
    var ar := ReversedArray(a);
    if HasIncreasingPair(ar) then
        var min_i := MinIndex(ar, n);
        n - min_i
    else
        0
}

// <vc-helpers>
function MinIndex(a: seq<int>, n: int): int
    requires n >= 1
    requires |a| == n
    requires ValidInput(n, a)
    requires HasIncreasingPair(ReversedArray(a))
    ensures 0 <= MinIndex(a, n) < n
    ensures var ar := ReversedArray(a); exists k_witness :: 0 <= k_witness < n && ar[k_witness] > ar[k_witness-1]
    ensures var ar := ReversedArray(a); (exists i_witness :: 1 <= i_witness < n && ar[i_witness] > ar[i_witness-1] && MinIndex(a, n) == i_witness)
    ensures var ar := ReversedArray(a); forall i :: 1 <= i < MinIndex(a, n) ==> ar[i] < ar[i-1]
{
    var ar := ReversedArray(a);
    var k := 1;
    while k < n
        invariant 1 <= k <= n
        invariant forall i :: 1 <= i < k ==> ar[i] <= ar[i-1]
    {
        if ar[k] > ar[k-1] then
            return k;
        k := k + 1;
    }
    0 // Should not be reached given HasIncreasingPair(ar)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures ValidOutput(n, result)
    ensures result == CorrectResult(n, a)
// </vc-spec>
// <vc-code>
{
    var ar := ReversedArray(a);
    if HasIncreasingPair(ar) then
        var min_i := MinIndex(a, n);
        return n - min_i;
    else
        return 0;
}
// </vc-code>

