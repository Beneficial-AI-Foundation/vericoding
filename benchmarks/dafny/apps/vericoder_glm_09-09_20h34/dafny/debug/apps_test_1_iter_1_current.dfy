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
function digitSumLE(x: int, y: int): bool
  requires x >= 0 && y >= 0
{
  digitSum(intToDigits(x)) <= digitSum(intToDigits(y))
}

lemma digitSumLE_antisymmetric(x: int, y: int)
  requires x >= 0 && y >= 0
  requires digitSumLE(x, y) && digitSumLE(y, x)
  ensures x == y
{
  assert digitSum(intToDigits(x)) == digitSum(intToDigits(y));
  var digits_x := intToDigits(x);
  var digits_y := intToDigits(y);
  assert |digits_x| == |digits_y|;
  if |digits_x| > 0 {
    assert digits_x[0] + digitSum(digits_x[1..]) == digits_y[0] + digitSum(digits_y[1..]);
    if digits_x[0] != digits_y[0] {
      assert false;
    }
    calc {
      digitSum(digits_x[1..]);
      digitSum(digits_x) - digits_x[0];
      digitSum(digits_y) - digits_y[0];
      { assert digits_x[0] == digits_y[0]; }
      digitSum(digits_y) - digits_x[0];
      digitSum(digits_y[1..]);
    }
    digitSumLE_antisymmetric(
      if x < 10 then 0 else x / 10,
      if y < 10 then 0 else y / 10
    );
    assert x / 10 == y / 10;
    assert x % 10 == y % 10;
    assert x == 10 * (x / 10) + x % 10;
    assert y == 10 * (y / 10) + y % 10;
    assert x == y;
  } else {
    assert x == 0 && y == 0;
  }
}

function maxDigitSum(x: int): int
  requires ValidInput(x)
{
  if x == 1 then 1
  else
    var prev_max := maxDigitSum(x - 1);
    var prev_max_sum := digitSum(intToDigits(prev_max));
    var curr_sum := digitSum(intToDigits(x));
    if curr_sum >= prev_max_sum then x else prev_max
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  var currentMax := 1;
  var i := 2;
  while i <= x
    invariant 2 <= i <= x + 1
    invariant 1 <= currentMax < i
    invariant ValidResult(i - 1, currentMax)
  {
    if digitSum(intToDigits(i)) >= digitSum(intToDigits(currentMax)) {
      currentMax := i;
    }
    i := i + 1;
  }
  result := currentMax;
}
// </vc-code>

