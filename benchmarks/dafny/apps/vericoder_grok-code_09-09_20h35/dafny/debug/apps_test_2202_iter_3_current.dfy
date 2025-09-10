predicate ValidInput(N: int, p: int, A: seq<int>)
{
    N >= 2 && p >= 2 && |A| == N && forall i :: 0 <= i < N ==> A[i] >= 1
}

function MaxSplitScore(A: seq<int>, p: int): int
    requires |A| >= 2
    requires p >= 2
{
    var scores := seq(|A| - 1, i requires 0 <= i < |A| - 1 => SplitScore(A, i + 1, p));
    MaxSeq(scores)
}

// <vc-helpers>
function Sum(s: seq<int>): int {
  if |s|==0 then 0 else s[0] + Sum(s[1..])
}

function SplitScore(A: seq<int>, split: int, p: int): int
  requires 1 <= split < |A|
{
  var left := A[..split]; var right := A[split..];
  var suml := Sum(left); var sumr := Sum(right);
  if suml % p == 0 && sumr % p == 0 then 1 else 0
}

function Max(a: int, b: int): int { if a > b then a else b }

function MaxSeq(s: seq<int>): int {
  if |s|==0 then 0 else if |s|==1 then s[0] else Max(s[0], MaxSeq(s[1..]))
}

predicate ValidInput(N: int, p: int, A: seq<int>)
{
    N >= 2 && p >= 2 && |A| == N && forall i :: 0 <= i < N ==> A[i] >= 1
}

function MaxSplitScore(A: seq<int>, p: int): int
    requires |A| >= 2
    requires p >= 2
{
    var scores := seq(|A| - 1, i requires 0 <= i < |A| - 1 => SplitScore(A, i + 1, p));
    MaxSeq(scores)
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, p: int, A: seq<int>) returns (result: int)
    requires ValidInput(N, p, A)
    ensures result >= 0
    ensures result < 2 * p
    ensures result == MaxSplitScore(A, p)
// </vc-spec>
// <vc-code>
{
  result := MaxSplitScore(A, p);
}
// </vc-code>

