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

// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  var best := 1;
  var maxSum := digitSum(intToDigits(1));
  var current := 2;
  while current <= x
    invariant 1 <= best <= current-1
    invariant best <= x
    invariant maxSum == digitSum(intToDigits(best))
    invariant forall y :: 1 <= y < current ==> digitSum(intToDigits(y)) <= maxSum
    invariant forall y :: 1 <= y < current && digitSum(intToDigits(y)) == maxSum ==> y <= best
  {
    var s_current := digitSum(intToDigits(current));
    if s_current > maxSum {
      maxSum := s_current;
      best := current;
    } else if s_current == maxSum && current > best {
      best := current;
    }
    current := current + 1;
  }
  return best;
}
// </vc-code>

