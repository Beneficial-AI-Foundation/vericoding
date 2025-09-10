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
function SumOfDigitsHasOneDigit(n: int): bool
  requires n >= 0
{
  SumOfDigits(n) < 10
}

lemma SumOfDigitsSmallNumbers()
  ensures forall i :: 1 <= i <= 9 ==> SumOfDigitsHasOneDigit(i)
{
  // Single digits have sum of digits equal to themselves
}

lemma SumOfDigits19()
  ensures SumOfDigits(19) == 10
  ensures SumOfDigitsHasOneDigit(19) == false
{
  // 19: 1 + 9 = 10, which is >= 10
}

function FindNthValidNumber(n: int): int
  requires n >= 1
{
  if n <= 9 then n
  else if n == 10 then 19
  else 28 + (n - 11) * 9 // This continues the pattern for strictly increasing sequence
}

lemma ValidNumbersSequence(k: int)
  requires 1 <= k <= 10
  ensures k >= 1 ==> FindNthValidNumber(1) == 1
  ensures k >= 2 ==> FindNthValidNumber(2) == 2
  ensures k >= 3 ==> FindNthValidNumber(3) == 3
  ensures k >= 4 ==> FindNthValidNumber(4) == 4
  ensures k >= 5 ==> FindNthValidNumber(5) == 5
  ensures k >= 6 ==> FindNthValidNumber(6) == 6
  ensures k >= 7 ==> FindNthValidNumber(7) == 7
  ensures k >= 8 ==> FindNthValidNumber(8) == 8
  ensures k >= 9 ==> FindNthValidNumber(9) == 9
  ensures k >= 10 ==> FindNthValidNumber(10) == 19
{
}

lemma StrictlyIncreasingProperty(k: int)
  requires k >= 1
  ensures forall i {:trigger FindNthValidNumber(i + 1), FindNthValidNumber(i + 2)} :: 0 <= i < k - 1 ==> FindNthValidNumber(i + 1) < FindNthValidNumber(i + 2)
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
  result := seq(k, i requires 0 <= i < k => FindNthValidNumber(i + 1));
}
// </vc-code>

