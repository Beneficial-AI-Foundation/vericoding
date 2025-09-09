/*
Given n threads initially ordered 1, 2, ..., n, after some messages are posted, 
the threads are reordered such that the thread now at position i was originally 
at position a_i. When a message is posted in a thread, that thread moves to the 
top of the list. Find the number of threads that must have received new messages.
A thread "surely has a new message" if there is no possible sequence of message 
posts that could result in the given reordering without that thread receiving a message.
*/

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
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures ValidOutput(n, result)
    ensures result == CorrectResult(n, a)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
