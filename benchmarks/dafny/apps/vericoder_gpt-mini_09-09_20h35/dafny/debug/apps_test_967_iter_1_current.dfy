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
function indexOf(ar: seq<int>, x: int, k: int): int
    requires 0 <= k < |ar|
    requires exists i :: k <= i < |ar| && ar[i] == x
    decreases |ar| - k
{
    if ar[k] == x then k else indexOf(ar, x, k + 1)
}

function MinIndex(ar: seq<int>, n: int): int
    requires |ar| == n && n >= 1
    requires exists i :: 0 <= i < n && ar[i] == 1
    ensures 1 <= MinIndex(ar, n) <= n
    ensures ar[MinIndex(ar, n) - 1] == 1
{
    indexOf(ar, 1, 0) + 1
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
    // find an index j in a where a[j] == 1 (exists by ValidInput)
    var j := choose i :: 0 <= i < n && a[i] == 1;
    var k := n - 1 - j;
    // witness that ar has a 1 at position k
    assert 0 <= k < n;
    assert ar[k] == a[n - 1 - k];
// </vc-code>

