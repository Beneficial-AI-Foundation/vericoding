function SumOfDigits(n: int): int
  requires n >= 0
{
  if n < 10 then n
  else (n % 10) + SumOfDigits(n / 10)
}

predicate ValidOutput(result: seq<int>, k: int)
{
  |result| == k &&
  (forall i :: 0 <= i < k ==> result[i] > 0) &&
  (forall i :: 0 <= i < k - 1 ==> result[i] < result[i + 1]) &&
  (k >= 1 ==> result[0] == 1) &&
  (k >= 2 ==> result[1] == 2) &&
  (k >= 3 ==> result[2] == 3) &&
  (k >= 4 ==> result[3] == 4) &&
  (k >= 5 ==> result[4] == 5) &&
  (k >= 6 ==> result[5] == 6) &&
  (k >= 7 ==> result[6] == 7) &&
  (k >= 8 ==> result[7] == 8) &&
  (k >= 9 ==> result[8] == 9) &&
  (k >= 10 ==> result[9] == 19)
}

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(k: int) returns (result: seq<int>)
  requires k >= 1
  ensures ValidOutput(result, k)
// </vc-spec>
// <vc-code>
{
  result := [];
  var idx := 1;
  while idx <= k
    invariant 0 <= idx <= k + 1 && |result| == idx - 1
    invariant idx >= 2 ==> result[0] == 1
    invariant idx >= 3 ==> result[1] == 2
    invariant idx >= 4 ==> result[2] == 3
    invariant idx >= 5 ==> result[3] == 4
    invariant idx >= 6 ==> result[4] == 5
    invariant idx >= 7 ==> result[5] == 6
    invariant idx >= 8 ==> result[6] == 7
    invariant idx >= 9 ==> result[7] == 8
    invariant idx >= 10 ==> result[8] == 9
    invariant idx >= 11 ==> result[9] == 19
    invariant forall j :: 0 <= j < |result| - 1 ==> result[j] < result[j + 1]
  {
    var next: int;
    if idx < 10 {
      next := idx;
    } else {
      next := (idx - 9) * 10 + 9;
    }
    result := result + [next];
    idx := idx + 1;
  }
}
// </vc-code>

