// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, d: int, t: seq<int>) returns (result: int)
  requires ValidInput(n, d, t)
  ensures ValidResult(n, d, t, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed compilation error related to `totalTime` helper. The previous iteration still had an unused `totalTime` helper, and the problem simply stated an invalid UnaryExpression. This iteration fixes the code by deleting the `totalTime` helper and implementing the necessary logic in the `solve` function directly based on the provided specifications. */
  var songSum := SumSeq(t);
  var minTime := MinTimeNeeded(n, t);

  if minTime > d {
    result := -1;
  } else {
    result := (d - songSum) / 5;
  }
}
// </vc-code>
