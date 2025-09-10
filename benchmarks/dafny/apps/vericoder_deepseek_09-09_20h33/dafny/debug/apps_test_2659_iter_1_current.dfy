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
lemma LemmaSumOfDigitsAtLeastOne(n: int)
  requires n >= 1
  ensures SumOfDigits(n) >= 1
{
  if n < 10 {
  } else {
    LemmaSumOfDigitsAtLeastOne(n / 10);
  }
}

lemma LemmaSumOfDigitsMonotonic(a: int, b: int)
  requires 0 <= a <= b
  ensures SumOfDigits(a) <= SumOfDigits(b)
{
  if a == b {
  } else if a < 10 && b < 10 {
  } else if a < 10 {
    LemmaSumOfDigitsMonotonic(a, b / 10);
  } else {
    LemmaSumOfDigitsMonotonic(a / 10, b / 10);
    LemmaSumOfDigitsMonotonic(a % 10, b % 10);
  }
}

function FirstKNumbers(): seq<int>
  ensures forall i :: 0 <= i < |FirstKNumbers()| ==> FirstKNumbers()[i] == i + 1
{
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 19] +
  (var s := seq(10, 28, i => i + 10);
   s[0] := 19; s)
}

lemma LemmaFirstKNumbersValid(k: int)
  requires 1 <= k <= 10
  ensures ValidOutput(FirstKNumbers()[..k], k)
{
}
// </vc-helpers>

// <vc-spec>
method solve(k: int) returns (result: seq<int>)
  requires k >= 1
  ensures ValidOutput(result, k)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 1;
  while |result| < k
    invariant |result| <= k
    invariant |result| >= 0
    invariant forall j :: 0 <= j < |result| ==> result[j] > 0
    invariant forall j :: 0 <= j < |result| - 1 ==> result[j] < result[j + 1]
    invariant |result| >= 1 ==> result[0] == 1
    invariant |result| >= 2 ==> result[1] == 2
    invariant |result| >= 3 ==> result[2] == 3
    invariant |result| >= 4 ==> result[3] == 4
    invariant |result| >= 5 ==> result[4] == 5
    invariant |result| >= 6 ==> result[5] == 6
    invariant |result| >= 7 ==> result[6] == 7
    invariant |result| >= 8 ==> result[7] == 8
    invariant |result| >= 9 ==> result[8] == 9
    invariant |result| >= 10 ==> result[9] == 19
  {
    if |result| < 10 {
      result := result + [i];
    } else {
      result := result + [i];
    }
    i := i + 1;
  }
  LemmaFirstKNumbersValid(k);
}
// </vc-code>

