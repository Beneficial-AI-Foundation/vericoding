Given n threads initially ordered 1, 2, ..., n, after some messages are posted, 
the threads are reordered such that the thread now at position i was originally 
at position a_i. When a message is posted in a thread, that thread moves to the 
top of the list. Find the number of threads that must have received new messages.
A thread "surely has a new message" if there is no possible sequence of message 
posts that could result in the given reordering without that thread receiving a message.

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

function MinIndex(ar: seq<int>, n: int): int
    requires n >= 1
    requires |ar| == n
    requires HasIncreasingPair(ar)
    ensures 1 <= MinIndex(ar, n) < n
    ensures ar[MinIndex(ar, n)] > ar[MinIndex(ar, n) - 1]
    ensures forall j :: 1 <= j < MinIndex(ar, n) ==> ar[j] <= ar[j-1]
{
    if n == 1 then 1
    else if ar[1] > ar[0] then 1
    else 1 + MinIndex(ar[1..], n-1)
}

method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures ValidOutput(n, result)
    ensures result == CorrectResult(n, a)
{
    var ar := ReversedArray(a);

    var ans := 0;
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant ans >= 0
        invariant ans <= n
        invariant forall j :: 1 <= j < i ==> ar[j] <= ar[j-1]
        invariant ans == 0 <==> forall j :: 1 <= j < i ==> ar[j] <= ar[j-1]
    {
        if ar[i] > ar[i-1] {
            ans := n - i;
            break;
        }
        i := i + 1;
    }

    result := ans;
}
