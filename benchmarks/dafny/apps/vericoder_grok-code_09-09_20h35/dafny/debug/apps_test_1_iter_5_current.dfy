function intToDigits(x: int): seq<int>
  requires x >= 0
{
  if x == 0 then [0]
  else intToDigitsHelper(x)
}

function intToDigitsHelper(x: int): seq<int>
  requires x > 0
  decreases x
{
  if x < 10 then [x]
  else intToDigitsHelper(x / 10) + [x % 10]
}

function digitSum(digits: seq<int>): int
{
  if |digits| == 0 then 0
  else digits[0] + digitSum(digits[1..])
}

predicate ValidInput(x: int)
{
  x >= 1
}

predicate ValidResult(x: int, result: int)
  requires ValidInput(x)
{
  result > 0 &&
  result <= x &&
  (forall y :: 1 <= y <= x ==> digitSum(intToDigits(y)) <= digitSum(intToDigits(result))) &&
  (forall y :: 1 <= y <= x && digitSum(intToDigits(y)) == digitSum(intToDigits(result)) ==> y <= result)
}

// <vc-helpers>
lemma DigitSumNonNegative(y: int)
  requires y >= 0
  ensures digitSum(intToDigits(y)) >= 0
{
  if y == 0
  {
  }
  else
  {
    assert intToDigits(y) == intToDigitsHelper(y);
    DigitSumNonNegative(y / 10);
    assert y %10 >=0;
  }
}

lemma DigitsNonNegative(y: int)
  requires y >= 0
  ensures forall k :: 0 <= k < |intToDigits(y)| ==> intToDigits(y)[k] >= 0
{
  if y == 0
  {
  }
  else
  {
    assert intToDigits(y) == intToDigitsHelper(y);
    DigitsNonNegative(y / 10);
    assert y %10 >=0;
  }
}

predicate IsBetter(newSum: int, newY: int, currMaxSum: int, currBest: int)
{
  newSum > currMaxSum || (newSum == currMaxSum && newY <= currBest)
}

lemma LoopInvariantIncrease(x: int)
  requires ValidInput(x)
  ensures true
{
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  result := x;
  DigitSumNonNegative(x);
  var maxDigSum := digitSum(intToDigits(x));
  var y := x - 1;
  while (y >= 1)
    invariant y >= 0
    invariant result >= 1 && result <= x
    invariant maxDigSum >= 0
    invariant forall i :: y < i <= x ==> digitSum(intToDigits(i)) <= digitSum(intToDigits(result))
    invariant forall i :: y < i <= x && digitSum(intToDigits(i)) == digitSum(intToDigits(result)) ==> i <= result
  {
    var currDigSum := digitSum(intToDigits(y));
    if (currDigSum > maxDigSum || (currDigSum == maxDigSum && y < result))
    {
      maxDigSum := currDigSum;
      result := y;
    }
    y := y - 1;
  }
}
// </vc-code>

