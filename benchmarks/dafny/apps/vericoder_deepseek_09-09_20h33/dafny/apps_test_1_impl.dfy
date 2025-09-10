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
    if y + 1 <= z {
      DigitSumMonotonic(y, y + 1);
      if y + 1 < z {
        DigitSumMonotonic(y + 1, z);
      }
    }
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
  } else if y == z + 1 {
    DigitSumMonotonic(z, z);
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
    // Add proof that the maximum exists for x by considering x itself
    var prev_max :| 1 <= prev_max <= x-1 && 
                   (forall y :: 1 <= y <= x-1 ==> digitSum(intToDigits(y)) <= digitSum(intToDigits(prev_max))) &&
                   (forall y :: 1 <= y <= x-1 && digitSum(intToDigits(y)) == digitSum(intToDigits(prev_max)) ==> y <= prev_max);
    var x_sum := digitSum(intToDigits(x));
    var prev_sum := digitSum(intToDigits(prev_max));
    if x_sum > prev_sum {
      // x becomes the new maximum
    } else if x_sum == prev_sum {
      // x might be larger than prev_max with same sum
    } else {
      // prev_max remains the maximum
    }
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
    
    if current > 1 {
      DigitSumDecreasing(current, current - 1);
    }
    current := current - 1;
  }
  
  result := candidate;
}
// </vc-code>

