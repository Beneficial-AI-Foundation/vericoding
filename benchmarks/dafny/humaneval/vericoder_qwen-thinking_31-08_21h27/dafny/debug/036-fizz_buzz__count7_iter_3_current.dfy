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
method count7(x: nat) returns (count: nat) 
  ensures count == count7_r(x)
{
  count := count7_r(x);
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
  return sum(seq(n, i => if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0));
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