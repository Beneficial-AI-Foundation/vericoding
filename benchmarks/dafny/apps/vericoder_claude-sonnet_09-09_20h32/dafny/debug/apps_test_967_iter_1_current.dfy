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
function MinIndex(ar: seq<int>, n: int): int
    requires |ar| == n >= 1
    requires HasIncreasingPair(ar)
    ensures 1 <= MinIndex(ar, n) < n
    ensures ar[MinIndex(ar, n)] > ar[MinIndex(ar, n) - 1]
    ensures forall j :: 1 <= j < MinIndex(ar, n) ==> ar[j] <= ar[j-1]
{
    MinIndexHelper(ar, n, 1)
}

function MinIndexHelper(ar: seq<int>, n: int, start: int): int
    requires |ar| == n >= 1
    requires 1 <= start < n
    requires exists i :: start <= i < n && ar[i] > ar[i-1]
    ensures start <= MinIndexHelper(ar, n, start) < n
    ensures ar[MinIndexHelper(ar, n, start)] > ar[MinIndexHelper(ar, n, start) - 1]
    ensures forall j :: start <= j < MinIndexHelper(ar, n, start) ==> ar[j] <= ar[j-1]
    decreases n - start
{
    if ar[start] > ar[start-1] then
        start
    else
        MinIndexHelper(ar, n, start + 1)
}

lemma MinIndexCorrectness(ar: seq<int>, n: int)
    requires |ar| == n >= 1
    requires HasIncreasingPair(ar)
    ensures 1 <= MinIndex(ar, n) < n
    ensures ar[MinIndex(ar, n)] > ar[MinIndex(ar, n) - 1]
    ensures forall j :: 1 <= j < MinIndex(ar, n) ==> ar[j] <= ar[j-1]
{
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

