predicate ValidInput(n: int, a: seq<int>) {
    n >= 1 && |a| == n
}

function simulateOperations(a: seq<int>): seq<int>
    requires |a| >= 1
    decreases |a|
{
    if |a| == 1 then 
        [a[0]]
    else
        var prev := simulateOperations(a[..|a|-1]);
        reverseSeq(prev + [a[|a|-1]])
}

function computeResult(a: seq<int>): seq<int>
    requires |a| >= 1
    ensures |computeResult(a)| == |a|
{
    var n := |a|;
    var o := seq(if n % 2 == 0 then n / 2 else (n + 1) / 2, i requires 0 <= i < (if n % 2 == 0 then n / 2 else (n + 1) / 2) => a[2*i]);
    var e := seq(n / 2, i requires 0 <= i < n / 2 => a[2*i + 1]);
    if n % 2 == 0 then
        reverseSeq(e) + o
    else
        reverseSeq(o) + e
}

function reverseSeq(s: seq<int>): seq<int>
    ensures |reverseSeq(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> reverseSeq(s)[i] == s[|s| - 1 - i]
{
    if |s| == 0 then []
    else reverseSeq(s[1..]) + [s[0]]
}

// <vc-helpers>
function OddLength(n: int): int
  requires n >= 1
  reads {}
  ensures OddLength(n) == (n+1)/2 when n%2 == 1
  ensures OddLength(n) == n/2 when n%2 == 0
{
  if n % 2 == 1 then (n + 1) / 2 else n / 2
}

function EvenLength(n: int): int
  requires n >= 1
  reads {}
  ensures EvenLength(n) == n/2 when n%2 == 1
  ensures EvenLength(n) == n/2 when n%2 == 0
{
  n / 2
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, a)
    ensures |result| == n
    ensures result == computeResult(a)
// </vc-spec>
// <vc-code>
{
    var o: seq<int>;
    var e: seq<int>;
    var oLength := OddLength(n);
    var eLength := EvenLength(n);

    if n % 2 == 0 {
        o := seq(oLength, i requires 0 <= i < oLength => a[2*i]);
        e := seq(eLength, i requires 0 <= i < eLength => a[2*i + 1]);
        result := reverseSeq(e) + o;
    } else {
        o := seq(oLength, i requires 0 <= i < oLength => a[2*i]);
        e := seq(eLength, i requires 0 <= i < eLength => a[2*i + 1]);
        result := reverseSeq(o) + e;
    }
}
// </vc-code>

