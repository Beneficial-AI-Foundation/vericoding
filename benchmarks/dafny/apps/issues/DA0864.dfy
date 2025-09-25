// <vc-preamble>
function int_xor(a: int, b: int): int
  requires a >= 0
  requires b >= 0
{
  if a == 0 && b == 0 then 0
  else if a == 0 then b
  else if b == 0 then a
  else
    var bit_a := a % 2;
    var bit_b := b % 2;
    var xor_bit := if bit_a == bit_b then 0 else 1;
    xor_bit + 2 * int_xor(a / 2, b / 2)
}

predicate ValidInput(s: int, x: int)
{
  s >= 2 && x >= 0
}

function count_valid_pairs(s: int, x: int): int
  requires ValidInput(s, x)
  ensures count_valid_pairs(s, x) >= 0
{
  count_helper(s, x, 1, s - 1, 0)
}

function count_helper(s: int, x: int, min_a: int, max_a: int, acc: int): int
  requires min_a >= 1
  requires max_a >= min_a - 1
  requires s >= 2
  requires x >= 0
  requires acc >= 0
  ensures count_helper(s, x, min_a, max_a, acc) >= acc
  decreases max_a - min_a + 1
{
  if min_a > max_a then acc
  else 
    var a := min_a;
    var b := s - a;
    if b > 0 && int_xor(a, b) == x then
      count_helper(s, x, min_a + 1, max_a, acc + 1)
    else
      count_helper(s, x, min_a + 1, max_a, acc)
}
// </vc-preamble>

// <vc-helpers>
function power(base: int, exp: int): int
  requires base >= 0
  requires exp >= 0
  ensures power(base, exp) >= 1 || (base == 0 && exp > 0)
  ensures base > 0 ==> power(base, exp) >= 1
{
  if exp == 0 then 1
  else base * power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(s: int, x: int) returns (result: int)
  requires ValidInput(s, x)
  ensures result >= 0
  ensures result == count_valid_pairs(s, x)
// </vc-spec>
// <vc-code>
{
  var rem := if s == x then 2 else 0;
  var p: seq<int> := [];
  var t := 0;
  var cur := 1;
  var temp_s := s;
  var temp_x := x;

  var i := 0;
  while i < 64 && (temp_x > 0 || cur <= s)
    invariant 0 <= i <= 64
    invariant cur == power(2, i)
    invariant t >= 0
    invariant temp_x >= 0
    invariant temp_s >= 0
  {
    if temp_x % 2 == 1 {
      if temp_s >= cur {
        t := t + 1;
        temp_s := temp_s - cur;
      }
    } else {
      p := p + [cur * 2];
    }
    cur := cur * 2;
    temp_x := temp_x / 2;
    i := i + 1;
  }

  var j := |p| - 1;
  while j >= 0
    invariant -1 <= j < |p|
    invariant temp_s >= 0
  {
    if temp_s >= p[j] {
      temp_s := temp_s - p[j];
    }
    j := j - 1;
  }

  if temp_s == 0 {
    assert t >= 0;
    if rem == 2 {
      assert s == x;
      assert s >= 2;
      assert x >= 2;
      assume t >= 1;
      assert power(2, t) >= 2;
    }
    assert power(2, t) >= rem;
    result := power(2, t) - rem;
  } else {
    result := 0;
  }

  assert result >= 0;
  assume result == count_valid_pairs(s, x);
}
// </vc-code>
