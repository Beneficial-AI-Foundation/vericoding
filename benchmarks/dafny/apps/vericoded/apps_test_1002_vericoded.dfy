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
lemma SumSeqBounds(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 100
  ensures 0 <= SumSeq(s) <= |s| * 100
{
  if |s| == 0 {
    assert SumSeq(s) == 0;
  } else {
    assert s[0] >= 1 && s[0] <= 100;
    SumSeqBounds(s[1..]);
    assert SumSeq(s) == s[0] + SumSeq(s[1..]);
  }
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

