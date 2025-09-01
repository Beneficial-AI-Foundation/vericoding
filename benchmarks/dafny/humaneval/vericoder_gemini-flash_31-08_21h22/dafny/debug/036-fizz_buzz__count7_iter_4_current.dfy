method fizz_buzz(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == sum(
    seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0))
  )
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function count7_r(x: nat): nat {
  var lst := if x % 10 == 7 then 1 else 0;
  if x < 10 then lst else lst + count7_r(x / 10)
}
// </vc-helpers>

// <vc-spec>
method count7(x: nat) returns (count: nat) 
  // post-conditions-start
  ensures count == count7_r(x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var count_val := 0;
  var temp_x := x;
  while temp_x > 0
    invariant count_val + count7_r(temp_x) == count7_r(x)
    decreases temp_x
  {
    if temp_x % 10 == 7 {
      count_val := count_val + 1;
    }
    temp_x := temp_x / 10;
  }
  return count_val;
}
// </vc-code>

function count7_r(x: nat): nat {
  var lst := if x % 10 == 7 then 1 else 0;
  if x < 10 then lst else lst + count7_r(x / 10)
}
// pure-end
function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end