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
lemma DigitSumPositive(n: int)
  requires n >= 1
  ensures digitSum(intToDigits(n)) > 0
{
  if n < 10 {
    assert intToDigits(n) == intToDigitsHelper(n) == [n];
    assert digitSum([n]) == n > 0;
  } else {
    var digits := intToDigits(n);
    assert digits == intToDigitsHelper(n);
    DigitSumHelperPositive(n);
  }
}

lemma DigitSumHelperPositive(n: int) 
  requires n >= 10
  ensures digitSum(intToDigitsHelper(n)) > 0
{
  var lastDigit := n % 10;
  var rest := n / 10;
  assert lastDigit >= 0;
  
  if rest < 10 {
    assert intToDigitsHelper(n) == [rest] + [lastDigit];
    assert digitSum([rest] + [lastDigit]) == rest + digitSum([lastDigit]) == rest + lastDigit;
    assert rest >= 1;
  } else {
    DigitSumHelperPositive(rest);
    assert digitSum(intToDigitsHelper(rest)) > 0;
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
  var maxSum := digitSum(intToDigits(1));
  var i := 2;
  
  while i <= x
    invariant 1 <= result <= i - 1
    invariant i >= 2
    invariant i <= x + 1
    invariant maxSum == digitSum(intToDigits(result))
    invariant forall y :: 1 <= y < i ==> digitSum(intToDigits(y)) <= maxSum
    invariant forall y :: 1 <= y < i && digitSum(intToDigits(y)) == maxSum ==> y <= result
  {
    var currentSum := digitSum(intToDigits(i));
    if currentSum > maxSum || (currentSum == maxSum && i > result) {
      result := i;
      maxSum := currentSum;
    }
    i := i + 1;
  }
  
  DigitSumPositive(result);
}
// </vc-code>

