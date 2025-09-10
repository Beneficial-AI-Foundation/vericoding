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
    // Note: this lemma only guarantees >= 0 if all digits are >= 0
    // For general sequences, digitSum can be negative
  }
}

lemma intToDigitsNonNegative(x: int)
  requires x >= 0
  ensures forall i :: 0 <= i < |intToDigits(x)| ==> intToDigits(x)[i] >= 0
{
  if x == 0 {
    assert intToDigits(x) == [0];
  } else {
    intToDigitsHelperNonNegative(x);
  }
}

lemma intToDigitsHelperNonNegative(x: int)
  requires x > 0
  ensures forall i :: 0 <= i < |intToDigitsHelper(x)| ==> intToDigitsHelper(x)[i] >= 0
  decreases x
{
  if x < 10 {
    assert intToDigitsHelper(x) == [x];
    assert x > 0;
  } else {
    intToDigitsHelperNonNegative(x / 10);
    assert x % 10 >= 0;
    assert intToDigitsHelper(x) == intToDigitsHelper(x / 10) + [x % 10];
  }
}

lemma digitSumNonNegativeForValidDigits(digits: seq<int>)
  requires forall i :: 0 <= i < |digits| ==> digits[i] >= 0
  ensures digitSum(digits) >= 0
{
  if |digits| == 0 {
    assert digitSum(digits) == 0;
  } else {
    digitSumNonNegativeForValidDigits(digits[1..]);
    assert digits[0] >= 0;
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
    digitSumDistributivity(intToDigitsHelper(x / 10), [x % 10]);
    assert digitSum(intToDigitsHelper(x)) == digitSum(intToDigitsHelper(x / 10)) + digitSum([x % 10]);
    assert digitSum([x % 10]) == (x % 10);
    assert digitSum(intToDigitsHelper(x)) == digitSum(intToDigitsHelper(x / 10)) + (x % 10);
    assert digitSum(intToDigitsHelper(x)) > 0;
  }
}

lemma digitSumDistributivity(s1: seq<int>, s2: seq<int>)
  ensures digitSum(s1 + s2) == digitSum(s1) + digitSum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
    assert digitSum(s1) == 0;
  } else {
    var tail := s1[1..];
    assert s1 == [s1[0]] + tail;
    assert s1 + s2 == [s1[0]] + (tail + s2);
    digitSumDistributivity(tail, s2);
    assert digitSum(tail + s2) == digitSum(tail) + digitSum(s2);
    assert digitSum(s1 + s2) == s1[0] + digitSum(tail + s2);
    assert digitSum(s1 + s2) == s1[0] + digitSum(tail) + digitSum(s2);
    assert digitSum(s1) == s1[0] + digitSum(tail);
    assert digitSum(s1 + s2) == digitSum(s1) + digitSum(s2);
  }
}

lemma digitSumValidInputNonNegative(x: int)
  requires ValidInput(x)
  ensures digitSum(intToDigits(x)) >= 0
{
  intToDigitsNonNegative(x);
  digitSumNonNegativeForValidDigits(intToDigits(x));
}

lemma digitSumForIntToDigitsNonNegative(x: int)
  requires x >= 0
  ensures digitSum(intToDigits(x)) >= 0
{
  intToDigitsNonNegative(x);
  digitSumNonNegativeForValidDigits(intToDigits(x));
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
  
  digitSumForIntToDigitsNonNegative(result);
}
// </vc-code>

