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
lemma lemma_MinTimeNeeded_SumSeq(n: int, t: seq<int>)
  requires |t| == n
  ensures MinTimeNeeded(n, t) == SumSeq(t) + 10 * (n - 1)
{
  // The definition of MinTimeNeeded is already SumSeq(t) + 10 * (n - 1),
  // so this lemma simply states that direct equality, which is useful
  // for the verifier to connect the definition.
}

lemma lemma_non_negative_result(n: int, d: int, t: seq<int>)
  requires ValidInput(n, d, t)
  requires MinTimeNeeded(n, t) <= d
  ensures (d - SumSeq(t)) / 5 >= 0
{
  // We know minTime = songSum + 10 * (n - 1)
  // If minTime <= d, then SumSeq(t) + 10 * (n - 1) <= d
  // d - SumSeq(t) >= 10 * (n - 1)
  // Since n >= 1 (from ValidInput), n-1 >= 0. So 10 * (n-1) >= 0.
  // Therefore d - SumSeq(t) >= 0.
  // The division 'div' in Dafny is Euclidean division.
  // Since d - SumSeq(t) >= 0, (d - SumSeq(t)) / 5 will also be >= 0.
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

  lemma_MinTimeNeeded_SumSeq(n, t); // Help the verifier connect the definition

  if minTime > d {
    result := -1;
  } else {
    lemma_non_negative_result(n, d, t); // Prove result >= 0 when minTime <= d
    result := (d - songSum) / 5;
  }
}
// </vc-code>

