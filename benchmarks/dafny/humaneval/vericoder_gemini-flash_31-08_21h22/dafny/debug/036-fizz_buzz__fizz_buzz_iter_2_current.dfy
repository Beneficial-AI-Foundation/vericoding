

// <vc-helpers>
function sum_seq_function(s: seq<nat>): nat
  reads s
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + sum_seq_function(s[1..])
}
// </vc-helpers>

// <vc-spec>
method fizz_buzz(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == sum(
    seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0))
  )
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var result_val: nat := 0;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result_val == sum(
      seq(i, idx requires 0 <= idx < i => (if idx % 11 == 0 || idx % 13 == 0 then (count7_r(idx) as int) else 0 as int))
    )
  {
    if (i % 11 == 0 || i % 13 == 0) {
      result_val := result_val + count7_r(i);
    }
    i := i + 1;
  }
  return result_val;
}
// </vc-code>

method count7(x: nat) returns (count: nat) 
  // post-conditions-start
  ensures count == count7_r(x)
  // post-conditions-end
{
  assume{:axiom} false;
}
function count7_r(x: nat): nat {
  var lst := if x % 10 == 7 then 1 else 0;
  if x < 10 then lst else lst + count7_r(x / 10)
}
// pure-end
function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end