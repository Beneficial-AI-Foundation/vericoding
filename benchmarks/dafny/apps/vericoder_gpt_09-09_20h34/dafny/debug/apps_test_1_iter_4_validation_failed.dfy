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
function sumDigits(n: int): int
  requires n >= 0
{
  digitSum(intToDigits(n))
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  var r := 1;
  var s := sumDigits(1);
  var i := 1;
  while i <= x
    invariant 1 <= i <= x + 1
    invariant 1 <= r <= x
    invariant s == sumDigits(r)
    invariant forall y :: 1 <= y < i ==> sumDigits(y) <= sumDigits(r)
    invariant forall y :: 1 <= y < i && sumDigits(y) == sumDigits(r) ==> y <= r
    decreases x - i + 1
  {
    var t := sumDigits(i);
    if t > s || (t == s && i > r) {
      r := i;
      s := t;
    }
    i := i + 1;
  }
  assert i > x;
  assert forall y :: 1 <= y <= x ==> digitSum(intToDigits(y)) <= digitSum(intToDigits(r)) by {
    var y: int;
    assume 1 <= y <= x;
    assert y < i;
    assert sumDigits(y) <= sumDigits(r);
    assert sumDigits(y) == digitSum(intToDigits(y));
    assert sumDigits(r) == digitSum(intToDigits(r));
    assert digitSum(intToDigits(y)) <= digitSum(intToDigits(r));
  };
  assert forall y :: 1 <= y <= x && digitSum(intToDigits(y)) == digitSum(intToDigits(r)) ==> y <= r by {
    var y: int;
    assume 1 <= y <= x && digitSum(intToDigits(y)) == digitSum(intToDigits(r));
    assert y < i;
    assert sumDigits(y) == digitSum(intToDigits(y));
    assert sumDigits(r) == digitSum(intToDigits(r));
    assert sumDigits(y) == sumDigits(r);
    assert y <= r;
  };
  result := r;
}
// </vc-code>

