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
  var i := 1;
  while i < x
    invariant 1 <= i <= x
    invariant 1 <= best <= i
    invariant forall y :: 1 <= y <= i ==> digitSum(intToDigits(y)) <= digitSum(intToDigits(best))
    invariant forall y :: 1 <= y <= i && digitSum(intToDigits(y)) == digitSum(intToDigits(best)) ==> y <= best
    decreases x - i
  {
    i := i + 1;
    var ds_i := digitSum(intToDigits(i));
    var ds_best := digitSum(intToDigits(best));
    if ds_i > ds_best || (ds_i == ds_best && i > best) {
      best := i;
    }
  }
  result := best;
}
// </vc-code>

