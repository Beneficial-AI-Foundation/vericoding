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
function sumDigits(x: int): int
  requires x >= 0
{
  digitSum(intToDigits(x))
}

lemma LessThan10(n: int)
  requires 0 <= n < 10
  ensures intToDigits(n) == [n]
{
  if n == 0 {
    assert intToDigits(0) == [0];
  } else {
    assert intToDigitsHelper(n) == [n];
  }
}

lemma IntToDigitsHelperProperty(x: int)
  requires x > 0
  ensures forall k: nat | 0 <= k < |intToDigitsHelper(x)| :: 0 <= intToDigitsHelper(x)[k] <= 9
  ensures |intToDigitsHelper(x)| > 0
{
  if x < 10 {
    assert intToDigitsHelper(x) == [x];
  } else {
    calc {
      intToDigitsHelper(x);
    }
    IntToDigitsHelperProperty(x / 10);
    assert forall k: nat | 0 <= k < |intToDigitsHelper(x / 10)| :: 0 <= intToDigitsHelper(x / 10)[k] <= 9;
    assert 0 <= x % 10 <= 9;
  }
}

lemma IntToDigitsProperty(x: int)
  requires x >= 0
  ensures forall k: nat | 0 <= k < |intToDigits(x)| :: 0 <= intToDigits(x)[k] <= 9
  ensures |intToDigits(x)| > 0
{
  if x == 0 {
    assert intToDigits(0) == [0];
    assert forall k | 0 <= k < |[0]| :: 0 <= [0][k] <= 9;
    assert |[0]| > 0;
  } else {
    IntToDigitsHelperProperty(x);
    assert forall k | 0 <= k < |intToDigitsHelper(x)| :: 0 <= intToDigitsHelper(x)[k] <= 9;
    assert |intToDigitsHelper(x)| > 0;
  }
}

lemma DigitSumProperty(digits: seq<int>)
  requires forall k | 0 <= k < |digits| :: 0 <= digits[k] <= 9
  ensures 0 <= digitSum(digits) <= 9 * |digits|
{
  if |digits| == 0 then
    assert digitSum(digits) == 0;
    assert 0 <= 0 <= 9 * 0;
  else
    DigitSumProperty(digits[1..]);
    assert 0 <= digits[0] <= 9;
    assert 0 <= digitSum(digits[1..]) <= 9 * (|digits|-1);
    assert 0 <= digits[0] + digitSum(digits[1..]) <= 9 + 9 * (|digits|-1);
    assert digits[0] + digitSum(digits[1..]) == digitSum(digits);
}

lemma DigitSumNonNegative(x: int)
  requires x >= 0
  ensures sumDigits(x) >= 0
{
  IntToDigitsProperty(x);
  DigitSumProperty(intToDigits(x));
  assert sumDigits(x) >= 0;
}

(* This lemma is not needed for the fixed code, as the constraint is on y >= result, not y == result *)
(*
lemma digitSumUniqueness(x: int, y: int)
  requires x > 0 && y > 0
  requires sumDigits(x) == sumDigits(y)
  ensures x == y
  decreases x, y
{
  // This lemma is generally false. For example, sumDigits(10) == 1 and sumDigits(1) == 1.
  // We need to implement the problem's logic, not prove universal properties.
  // The problem implies an ordering tie-breaking rule if sums are equal (y <= `result`).
}
*)
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  var min_sum_val := sumDigits(1);
  var result_val := 1;

  var current := 2;
  while current <= x
    invariant 1 <= current <= x + 1
    invariant 1 <= result_val < current
    invariant min_sum_val == sumDigits(result_val)
    invariant 0 <= min_sum_val
    invariant forall y :: 1 <= y < current ==> sumDigits(result_val) <= sumDigits(y)
    invariant forall y :: 1 <= y < current && sumDigits(y) == sumDigits(result_val) ==> y >= result_val
    decreases x - current
  {
    var current_sum := sumDigits(current);

    if current_sum < min_sum_val {
      min_sum_val := current_sum;
      result_val := current;
    } else if current_sum == min_sum_val {
      if current < result_val { // Tie-breaking rule: smaller number
        result_val := current;
      }
    }
    current := current + 1;
  }
  result := result_val;

  // Post-condition proof (requires careful reasoning about the invariants)
  // Ensure result > 0
  assert result > 0;
  // Ensure result <= x
  assert result <= x;

  // Ensure (forall y :: 1 <= y <= x ==> digitSum(intToDigits(y)) <= digitSum(intToDigits(result)))
  assert forall y :: 1 <= y <= x ==> sumDigits(result) <= sumDigits(y)
    by {
      var y: int;
      forall y | 1 <= y <= x
        ensures sumDigits(result) <= sumDigits(y)
      {
        if y < current { // y was processed in the loop
          assert sumDigits(result_val) <= sumDigits(y); // This is from the invariant for y < current
        } else { // y is the final `x` and current is `x+1`
                 // The result_val holds the correct minimum up to x.
          assert y == x;
          assert current == x + 1; // current is x+1 at loop termination
          assert sumDigits(result_val) <= sumDigits(x);
        }
      }
    }
  ;

  // Ensure (forall y :: 1 <= y <= x && digitSum(intToDigits(y)) == digitSum(intToDigits(result)) ==> y <= result)
  assert forall y :: 1 <= y <= x && sumDigits(y) == sumDigits(result) ==> y >= result
    by {
      var y: int;
      forall y | 1 <= y <= x && sumDigits(y) == sumDigits(result)
        ensures y >= result
      {
        if y < current { // y was handled in the loop
          assert y >= result_val;
        } else { // y is the final `x` and current is `x+1`
          assert y == x;
          assert current == x + 1;
          assert x >= result_val;
        }
      }
    }
  ;
}
// </vc-code>

