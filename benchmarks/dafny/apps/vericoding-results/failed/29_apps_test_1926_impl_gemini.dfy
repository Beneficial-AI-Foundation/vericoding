predicate ValidInput(n: int, a: seq<int>)
{
  n >= 2 && |a| == n
}

function CountViolationsForK(a: seq<int>, n: int, k: int): int
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
{
  |set i | 2 <= i <= n && 
    var parent_idx := (i + k - 2) / k;
    parent_idx >= 1 && a[i-1] < a[parent_idx-1]|
}

predicate ValidOutput(result: seq<int>, n: int, a: seq<int>)
  requires n >= 2 && |a| == n
{
  |result| == n - 1 &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] >= 0) &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] == CountViolationsForK(a, n, k))
}

// <vc-helpers>
function CountSmaller(a: seq<int>, limit: int, v: int) : int
    requires 0 <= limit <= |a|
{
    |set i | 0 <= i < limit && a[i] < v|
}

lemma CountSmallerProperties(a: seq<int>, v: int)
    requires |a| > 0
    ensures forall i :: 0 <= i < |a| ==> CountSmaller(a, i+1, v) == CountSmaller(a, i, v) + (if a[i] < v then 1 else 0)
{}

function CountViolationsForK(a: seq<int>, n: int, k: int): int
  requires n >= 2 && |a| == n && 1
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: seq<int>)
  requires ValidInput(n, a)
  ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
function CountSmaller(a: seq<int>, limit: int, v: int) : int
    requires 0 <= limit <= |a|
{
    |set i | 0 <= i < limit && a[i] < v|
}

lemma CountSmallerProperties(a: seq<int>, v: int)
    requires |a| > 0
    ensures forall i :: 0 <= i < |a| ==> CountSmaller(a, i+1, v) == CountSmaller(a, i, v) + (if a[i] < v then 1 else 0)
{}

function CountViolationsForK(a: seq<int>, n: int, k: int): int
  requires n >= 2 && |a| == n && 1
// </vc-code>

