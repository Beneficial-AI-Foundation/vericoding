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
    ensures k <= indexOf(ar, x, k) < |ar|
    ensures ar[indexOf(ar, x, k)] == x
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

lemma ReversedContainsOne(n: int, a: seq<int>)
    requires ValidInput(n, a)
    ensures exists i :: 0 <= i < n && ReversedArray(a)[i] == 1
{
    var j := indexOf(a, 1, 0);
    assert 0 <= j < n;
    var k := n - 1 - j;
    assert 0 <= k < n;
    // By definition of ReversedArray: ReversedArray(a)[k] == a[n-1-k]
    assert ReversedArray(a)[k] == a[n - 1 - k];
    assert a[j] == 1;
    assert ReversedArray(a)[k] == 1;
    assert exists i :: 0 <= i < n && ReversedArray(a)[i] == 1;
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
  assert ar == ReversedArray(a);
  if HasIncreasingPair(ar) {
    assert |ar| == n;
    assert n >= 1;
    ReversedContainsOne(n, a);
    assert ar == ReversedArray(a);
    assert exists i :: 0 <= i < n && ar[i] == 1;
    var min_i := MinIndex(ar, n);
    result := n - min_i;
    assert result == CorrectResult(n, a);
  } else {
    result := 0;
    assert result == CorrectResult(n, a);
  }
}
// </vc-code>

