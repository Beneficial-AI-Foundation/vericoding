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
lemma DigitSumMonotonic(y: int, z: int)
  requires y >= 0 && z >= 0
  requires y <= z
  ensures digitSum(intToDigits(y)) <= digitSum(intToDigits(z))
  decreases z - y
{
  if y < z {
    var next := y + 1;
    DigitSumMonotonic(y, next);
    DigitSumMonotonic(next, z);
  }
}

lemma DigitSumDecreasing(y: int, z: int)
  requires y >= 0 && z >= 0
  requires y > z
  ensures digitSum(intToDigits(y)) >= digitSum(intToDigits(z))
  decreases y - z
{
  if y > z + 1 {
    var prev := y - 1;
    DigitSumDecreasing(y, prev);
    DigitSumDecreasing(prev, z);
  }
}

lemma MaxDigitSumExists(x: int)
  requires x >= 1
  ensures exists result: int :: 
    1 <= result <= x && 
    (forall y :: 1 <= y <= x ==> digitSum(intToDigits(y)) <= digitSum(intToDigits(result))) &&
    (forall y :: 1 <= y <= x && digitSum(intToDigits(y)) == digitSum(intToDigits(result)) ==> y <= result)
  decreases x
{
  if x == 1 {
    // Base case: only one number
  } else {
    MaxDigitSumExists(x - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  var current := x;
  var maxSum := digitSum(intToDigits(x));
  var candidate := x;
  
  while current >= 1
    decreases current
    invariant current >= 0
    invariant candidate >= 1 && candidate <= x
    invariant maxSum == digitSum(intToDigits(candidate))
    invariant forall y :: current < y <= x ==> digitSum(intToDigits(y)) <= maxSum
    invariant forall y :: current < y <= x && digitSum(intToDigits(y)) == maxSum ==> y <= candidate
  {
    var currentSum := digitSum(intToDigits(current));
    if currentSum > maxSum {
      maxSum := currentSum;
      candidate := current;
    } else if currentSum == maxSum && current > candidate {
      candidate := current;
    }
    current := current - 1;
  }
  
  result := candidate;
}
// </vc-code>

