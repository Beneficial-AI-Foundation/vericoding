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
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures SumSeq(s) >= 0
{
  if |s| > 0 {
    assert s[0] >= 1;
    SumSeqNonNegative(s[1..]);
    assert SumSeq(s) == s[0] + SumSeq(s[1..]);
    assert SumSeq(s[1..]) >= 0;
  }
}

lemma SumSeqTail(s: seq<int>)
  requires |s| > 0
  ensures SumSeq(s) == s[0] + SumSeq(s[1..])
{
}

lemma MinTimeNeededProperty(n: int, t: seq<int>)
  requires |t| == n
  ensures MinTimeNeeded(n, t) == SumSeq(t) + 10 * (n - 1)
{
}

lemma DivProperty(a: int, b: int)
  requires a >= 0 && b > 0
  ensures a / b >= 0
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
  var totalSongTime := SumSeq(t);
  SumSeqNonNegative(t);
  var minRequiredTime := totalSongTime + 10 * (n - 1);
  
  if minRequiredTime > d {
    result := -1;
  } else {
    var availableJokeTime := d - totalSongTime;
    assert availableJokeTime >= 0;
    DivProperty(availableJokeTime, 5);
    var maxJokes := availableJokeTime / 5;
    result := maxJokes;
  }
}
// </vc-code>

