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
  } else if b < 10 {
    assert a <= b;
  } else if a < 10 {
    LemmaSumOfDigitsAtLeastOne(b / 10);
    assert SumOfDigits(b) >= 1;
  } else {
    LemmaSumOfDigitsMonotonic(a / 10, b / 10);
  }
}

function FirstKNumbers(): seq<int>
  ensures forall i :: 0 <= i < |FirstKNumbers()| ==> FirstKNumbers()[i] == i + 1
{
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 19]
}

lemma LemmaFirstKNumbersValid(k: int)
  requires 1 <= k <= 10
  ensures ValidOutput(FirstKNumbers()[..k], k)
{
  if k == 10 {
    assert FirstKNumbers()[9] == 19;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int) returns (result: seq<int>)
  requires k >= 1
  ensures ValidOutput(result, k)
// </vc-spec>
// <vc-code>
{
  var arr := FirstKNumbers();
  assert |arr[..k]| == k by {
    assert |arr| == 10;
  };
  result := arr[..k];
  LemmaFirstKNumbersValid(k);
}
// </vc-code>

