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
// Helper lemma to prove that digitSum(intToDigits(y)) >= 0
lemma DigitSumNonNegative(y: int)
  requires y >= 0
  ensures digitSum(intToDigits(y)) >= 0
{
  // Proof by induction on length of digits
  if y == 0
  {
  }
  else
  {
    assert intToDigits(y) == intToDigitsHelper(y);
    DigitSumNonNegative(y / 10);  // Inductive hypothesis
  }
}

// Helper lemma to prove that intToDigits(y) produces non-negative digits
lemma DigitsNonNegative(y: int)
  requires y >= 0
  ensures forall k :: 0 <= k < |intToDigits(y)| ==> intToDigits(y)[k] >= 0
{
  // Proof by induction
  if y == 0
  {
  }
  else
  {
    assert intToDigits(y) == intToDigitsHelper(y);
    DigitsNonNegative(y / 10);  // Inductive hypothesis
    assert forall k :: 0 <= k < |intToDigits(y)| - 1 ==> intToDigits(y)[k] >= 0;
    assert intToDigits(y)[|intToDigits(y)| - 1] == y % 10 >= 0;
  }
}

// Helper predicate to check if a candidate is better
predicate IsBetter(newSum: int, newY: int, currMaxSum: int, currBest: int)
{
  newSum > currMaxSum || (newSum == currMaxSum && newY <= currBest)
}

// Lemma to establish invariant properties; add more if needed for loop verification
lemma LoopInvariantIncrease(x: int)
  requires ValidInput(x)
  ensures true  // Placeholder for potential refinements
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
  maxDigSum := digitSum(intToDigits(x));
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

