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
  result := 1;
  var bestSum := digitSum(intToDigits(1));
  var i := 2;
  while i <= x
    invariant 1 <= result <= x
    invariant 2 <= i <= x + 1
    invariant bestSum == digitSum(intToDigits(result))
    invariant (forall y :: 1 <= y < i ==> digitSum(intToDigits(y)) <= bestSum)
    invariant (forall y :: 1 <= y < i && digitSum(intToDigits(y)) == bestSum ==> y <= result)
    decreases x - i + 1
  {
    var s := digitSum(intToDigits(i));
    if s > bestSum || (s == bestSum && i > result) {
      result := i;
      bestSum := s;
    }
    i := i + 1;
  }
}
// </vc-code>

