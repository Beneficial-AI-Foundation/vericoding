function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + SumSeq(s[1..])
}

predicate ValidInput(n: int, d: int, t: seq<int>)
{
  1 <= n <= 100 && 1 <= d <= 10000 &&
  |t| == n &&
  forall i :: 0 <= i < |t| ==> 1 <= t[i] <= 100
}

function MinTimeNeeded(n: int, t: seq<int>): int
  requires |t| == n
{
  SumSeq(t) + 10 * (n - 1)
}

predicate ValidResult(n: int, d: int, t: seq<int>, result: int)
  requires ValidInput(n, d, t)
{
  var songSum := SumSeq(t);
  var minTime := MinTimeNeeded(n, t);
  if minTime > d then
    result == -1
  else
    result == (d - songSum) / 5 && result >= 0
}

// <vc-helpers>
lemma SumSeqNonNegative(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures SumSeq(s) >= 0
{
  if |s| == 0 {
  } else {
    SumSeqNonNegative(s[1..]);
  }
}

lemma SumSeqBounds(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 100
  ensures SumSeq(s) >= |s| && SumSeq(s) <= 100 * |s|
{
  if |s| == 0 {
  } else {
    SumSeqBounds(s[1..]);
  }
}

lemma MinTimeNeededBounds(n: int, t: seq<int>)
  requires ValidInput(n, 1, t)
  ensures MinTimeNeeded(n, t) >= n + 10 * (n - 1)
  ensures MinTimeNeeded(n, t) <= 100 * n + 10 * (n - 1)
{
  SumSeqBounds(t);
}

lemma DivisionProperties(a: int, b: int)
  requires b > 0
  ensures (a / b) * b <= a < (a / b + 1) * b
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, d: int, t: seq<int>) returns (result: int)
  requires ValidInput(n, d, t)
  ensures ValidResult(n, d, t, result)
// </vc-spec>
// <vc-code>
{
  var songSum := SumSeq(t);
  var minTime := MinTimeNeeded(n, t);
  
  if minTime > d {
    result := -1;
  } else {
    result := (d - songSum) / 5;
  }
}
// </vc-code>

