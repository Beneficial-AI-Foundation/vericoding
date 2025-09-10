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
lemma digitSumNonNegative(digits: seq<int>)
  ensures digitSum(digits) >= 0
{
  if |digits| == 0 {
    assert digitSum(digits) == 0;
  } else {
    digitSumNonNegative(digits[1..]);
    assert digitSum(digits[1..]) >= 0;
    assert digitSum(digits) == digits[0] + digitSum(digits[1..]);
  }
}

lemma digitSumPositiveForPositive(x: int)
  requires x > 0
  ensures digitSum(intToDigits(x)) > 0
{
  var digits := intToDigits(x);
  if x == 0 {
  } else {
    var helperDigits := intToDigitsHelper(x);
    assert digits == helperDigits;
    digitSumPositiveForPositiveHelper(x);
  }
}

lemma digitSumPositiveForPositiveHelper(x: int)
  requires x > 0
  ensures digitSum(intToDigitsHelper(x)) > 0
  decreases x
{
  if x < 10 {
    assert intToDigitsHelper(x) == [x];
    assert digitSum([x]) == x + digitSum([]);
    assert digitSum([]) == 0;
    assert digitSum([x]) == x;
    assert x > 0;
  } else {
    digitSumPositiveForPositiveHelper(x / 10);
    assert digitSum(intToDigitsHelper(x / 10)) > 0;
    assert x % 10 >= 0;
    assert intToDigitsHelper(x) == intToDigitsHelper(x / 10) + [x % 10];
    assert digitSum(intToDigitsHelper(x)) == digitSum(intToDigitsHelper(x / 10)) + (x % 10);
    assert digitSum(intToDigitsHelper(x)) > 0;
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
  result := 1;
  var current := 1;
  var maxSum := digitSum(intToDigits(1));
  
  digitSumPositiveForPositive(1);
  
  while current < x
    invariant 1 <= current <= x
    invariant 1 <= result <= current
    invariant maxSum == digitSum(intToDigits(result))
    invariant maxSum > 0
    invariant forall y :: 1 <= y <= current ==> digitSum(intToDigits(y)) <= maxSum
    invariant forall y :: 1 <= y <= current && digitSum(intToDigits(y)) == maxSum ==> y <= result
  {
    current := current + 1;
    digitSumPositiveForPositive(current);
    var currentSum := digitSum(intToDigits(current));
    
    if currentSum > maxSum || (currentSum == maxSum && current > result) {
      result := current;
      maxSum := currentSum;
    }
  }
}
// </vc-code>

