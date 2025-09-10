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
function MinIndex(ar: seq<int>, n: int): (idx: int)
    requires |ar| == n && n >= 1
    requires HasIncreasingPair(ar)
    ensures 1 <= idx < n
    ensures ar[idx] > ar[idx-1]
    ensures forall j :: 1 <= j < n && ar[j] > ar[j-1] ==> ar[idx] <= ar[j]
{
    var i := 1;
    var min_val := ar[1];
    var min_idx := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant min_val == ar[min_idx]
        invariant 1 <= min_idx < n
        invariant ar[min_idx] > ar[min_idx-1]
        invariant forall j :: 1 <= j < i && ar[j] > ar[j-1] ==> ar[min_idx] <= ar[j]
    {
        if ar[i] > ar[i-1] && ar[i] < min_val {
            min_val := ar[i];
            min_idx := i;
        }
        i := i + 1;
    }
    min_idx
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
    if HasIncreasingPair(ar) {
        var min_i := MinIndex(ar, n);
        result := n - min_i;
    } else {
        result := 0;
    }
}
// </vc-code>

