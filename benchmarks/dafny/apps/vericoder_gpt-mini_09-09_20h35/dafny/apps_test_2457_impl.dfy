predicate ValidInput(input: string) {
    |input| >= 0
}

predicate ValidTestCase(n: int, a: int, b: int, c: int, d: int) {
    n >= 1 && n <= 1000 &&
    a >= 0 && a <= 1000 &&
    b >= 0 && b < a &&
    c >= 0 && c <= 1000 &&
    d >= 0 && d < c
}

function CanAchieveWeight(n: int, a: int, b: int, c: int, d: int): bool {
    var minWeight := (a - b) * n;
    var maxWeight := (a + b) * n;
    var targetMin := c - d;
    var targetMax := c + d;
    !(minWeight > targetMax || maxWeight < targetMin)
}

predicate ValidOutput(output: string) {
    forall i :: 0 <= i < |output| ==> output[i] in "YesNo\n"
}

// <vc-helpers>
function Digit(c: char): int
  requires c >= '0' && c <= '9'
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else 9
}

method ParseNonnegatives(s: string) returns (nums: seq<int>)
  ensures forall x :: x in nums ==> x >= 0
{
  nums := [];
  var cur: int := 0;
  var inNum: bool := false;
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall x :: x in nums ==> x >= 0
    decreases |s| - i
  {
    var c: char := s[i];
    if c >= '0' && c <= '9' {
      var digit: int := Digit(c);
      cur := cur * 10 + digit;
      inNum := true;
    } else {
      if inNum {
        nums := nums + [cur];
        cur := 0;
        inNum := false;
      }
    }
    i := i + 1;
  }
  if inNum {
    nums := nums + [cur];
  }
}

lemma BoundsForIndices(nums: seq<int>, t: int)
  requires t >= 0
  requires |nums| >= 1 + t * 5
  ensures forall i :: 0 <= i < t ==> (1 + i * 5) + 4 < |nums|
{
  if t > 0 {
    var i := 0;
    while i < t
      invariant 0 <= i <= t
      decreases t - i
    {
      // (1 + i*5) + 4 = 5*(i+1) and i+1 <= t, so 5*(i+1) <= 5*t = (1 + t*5) - 1 < |nums|
      assert (1 + i * 5) + 4 == 5 * (i + 1);
      assert i + 1 <= t;
      assert 5 * (i + 1) <= 5 * t;
      assert 5 * t == (1 + t * 5) - 1;
      assert (1 + i * 5) + 4 <= (1 + t * 5) - 1;
      assert (1 + i * 5) + 4 < |nums|;
      i := i + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures (input == "" || input == "\n") ==> result == ""
    ensures input != "" && input != "\n" ==> (|result| > 0 ==> result[|result|-1] == '\n' || (|result| > 3 && result[|result|-4..] in ["Yes\n", "No\n"]))
// </vc-spec>
// <vc-code>
{
  if input == "" || input == "\n" {
    return "";
  }
  var nums := ParseNonnegatives(input);
  if |nums| == 0 {
    return "";
  }
  var t := nums[0];
  if t <= 0 {
    return "";
  }
  if |nums| < 1 + t * 5 {
    return "";
  }
  // Help the verifier: establish the necessary bound for all iterations
  BoundsForIndices(nums, t);

  var res := "";
  var i := 0;
  var idx := 1;
  while i < t
    invariant 0 <= i <= t
    invariant idx == 1 + i * 5
    invariant idx + 4 < |nums|
    decreases t - i
  {
    var n := nums[idx];
    var a := nums[idx + 1];
    var b := nums[idx + 2];
    var c := nums[idx + 3];
    var d := nums[idx + 4];
    if CanAchieveWeight(n, a, b, c, d) {
      res := res + "Yes\n";
    } else {
      res := res + "No\n";
    }
    i := i + 1;
    idx := idx + 5;
  }
  return res;
}
// </vc-code>

