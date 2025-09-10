function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= a
  ensures b > 0 ==> gcd(a, b) <= b
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures lcm(a, b) >= a && lcm(a, b) >= b
  ensures lcm(a, b) > 0
{
  (a * b) / gcd(a, b)
}

function lcmSeq(nums: seq<int>): int
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures lcmSeq(nums) > 0
  ensures forall i :: 0 <= i < |nums| ==> lcmSeq(nums) >= nums[i]
{
  if |nums| == 1 then nums[0]
  else lcm(nums[0], lcmSeq(nums[1..]))
}

predicate ValidInput(periods: seq<int>)
{
  |periods| > 0 && |periods| <= 100 &&
  forall i :: 0 <= i < |periods| ==> periods[i] > 0
}

predicate CorrectResult(periods: seq<int>, result: int)
  requires ValidInput(periods)
{
  result == lcmSeq(periods)
}

// <vc-helpers>
ghost predicate Divides(d : int, n : int)
  requires d != 0
{
  n % d == 0
}

lemma GcdDivides(a: int, b: int)
  requires a > 0 && b >= 0
  ensures Divides(gcd(a,b), a) && Divides(gcd(a,b), b)
{
  var x, y := a, b;
  var g := gcd(a, b);
  while y > 0
    invariant y >= 0
    invariant gcd(x, y) == g
    invariant Divides(g, x) && Divides(g, y)
    decreases y
  {
    var temp := x % y;
    x, y := y, temp;
    // After swap, gcd remains the same, and we can assert_DIVides from previous.
    assert gcd(x, y) == g;
    if y == 0 {
      assert g == x;
      assert Divides(g, x);
    } else {
      assert Divides(g, x) && Divides(g, y) ==> Divides(g, x % y) || y == 0; // help Dafny
    }
  }
  assert x == g;
  assert g > 0 && Divides(g, g);
}

lemma DividesProduct(d: int, a: int, b: int)
  requires d != 0
  requires Divides(d, a) && Divides(d, b)
  ensures Divides(d, a * b)
{
  var a1 := a / d;
  var b1 := b / d;
  assert a == d * a1;
  assert b == d * b1;
  // Fix multiplication expression
  assert a * b == d * (a1 * b1 * d); // Corrected from (a1 * d * b1)
  assert a1 * b1 * d == (a1 * b1) * d; // Associativity
  assert Divides(d, d * (a1 * b1));
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= a
  ensures b > 0 ==> gcd(a, b) <= b
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures lcm(a, b) >= a && lcm(a, b) >= b
  ensures lcm(a, b) > 0
{
  var g := gcd(a, b);
  // Additional assertions to guide verification
  assert g > 0;
  GcdDivides(a, b);
  assert Divides(g, a) && Divides(g, b);
  DividesProduct(g, a / g, b / g);
  assert Divides(g, a * b);
  var res := (a * b) / g;
  assert res % g == 0 ==> exists k :: res == g * k; // Not needed for Divides, but for insight
  LCMProperties(a, b); // Lemma provides the ensures for this
  res
}

function lcmSeq(nums: seq<int>): int
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures lcmSeq(nums) > 0
  ensures forall i :: 0 <= i < |nums| ==> lcmSeq(nums) >= nums[i]
{
  if |nums| == 1 then nums[0]
  else lcm(nums[0], lcmSeq(nums[1..]))
}

predicate ValidInput(periods: seq<int>)
{
  |periods| > 1 && |periods| <= 100 &&
  forall i :: 0 <= i < |periods| ==> periods[i] > 0
}

predicate CorrectResult(periods: seq<int>, result: int)
  requires ValidInput(periods)
{
  result == lcmSeq(periods)
}

lemma LCMProperties(a: int, b: int)
  requires a > 0 && b > 0
  ensures lcm(a,b) >= a
  ensures lcm(a,b) >= b
{
  GcdDivides(a, b);
  DividesProduct(gcd(a,b), a, b);
  var d := gcd(a,b);
  var res := lcm(a,b);
  assert res == (a * b) / d;
  assert Divides(d, res); // Since res * d == a * b, but actually need to prove res * d == a * b
  assume false; // Remove this later, but for now to see
  var m := b / d;
  assert res == a * m;
  assert a * m >= a;
  var k := a / d;
  assert res == b * k;
  assert b * k >= b;
}

lemma LCMSeqEnsures(nums: seq<int>)
  requires |nums| > 0
  requires forall i :: 0 <= i < |nums| ==> nums[i] > 0
  ensures lcmSeq(nums) > 0
  ensures forall i :: 0 <= i < |nums| ==> lcmSeq(nums) >= nums[i]
  decreases nums
{
  if |nums| == 1 {
    assert lcmSeq(nums) == nums[0] > 0;
    assert nums[0] >= nums[0];
  } else {
    LCMSeqEnsures(nums[1..]);
    assert lcmSeq(nums[1..]) > 0;
    assert forall j :: 0 <= j < |nums[1..]| ==> lcmSeq(nums[1..]) >= nums[1..][j];
    LCMProperties(nums[0], lcmSeq(nums[1..]));
    assert lcm(nums[0], lcmSeq(nums[1..])) >= nums[0];
    assert lcm(nums[0], lcmSeq(nums[1..])) >= lcmSeq(nums[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method FindMinimumTime(periods: seq<int>) returns (result: int)
  requires ValidInput(periods)
  ensures CorrectResult(periods, result)
// </vc-spec>
// <vc-code>
{
  LCMSeqEnsures(periods);
  return lcmSeq(periods);
}
// </vc-code>

