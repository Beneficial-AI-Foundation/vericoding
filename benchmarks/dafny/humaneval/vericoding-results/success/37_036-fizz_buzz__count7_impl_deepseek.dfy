// <vc-preamble>
function count7_r(x: nat): nat {
  var lst := if x % 10 == 7 then 1 else 0;
  if x < 10 then lst else lst + count7_r(x / 10)
}

function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// </vc-preamble>

// <vc-helpers>
function digit_to_int(d: char): int
  requires '0' <= d <= '9'
{
  d as int - '0' as int
}
// </vc-helpers>

// <vc-spec>
method count7(x: nat) returns (count: nat) 

  ensures count == count7_r(x)
// </vc-spec>
// <vc-code>
{
  var x_copy := x;
  count := 0;
  
  while x_copy > 0
    invariant count == count7_r(x) - count7_r(x_copy)
    invariant x_copy >= 0
  {
    var digit := x_copy % 10;
    if digit == 7 {
      count := count + 1;
    }
    x_copy := x_copy / 10;
  }
}
// </vc-code>
