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
function count7_recursive(x: nat): nat {
  var lst := if x % 10 == 7 then 1 else 0;
  if x < 10 then lst else lst + count7_recursive(x / 10)
}

function sum_seq(s: seq<int>): int {
  if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method count7(x: nat) returns (count: nat)
Count occurrences. Ensures: returns the correct value.
*/
// </vc-description>

// <vc-spec>
method count7(x: nat) returns (count: nat)
  ensures count == count7_recursive(x)
// </vc-spec>
// <vc-code>
{
  var result := 0;
  var temp := x;
  while temp > 0
    invariant result == count7_recursive(x) - count7_recursive(temp)
  {
    if temp % 10 == 7 {
      result := result + 1;
    }
    temp := temp / 10;
  }
  count := result;
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