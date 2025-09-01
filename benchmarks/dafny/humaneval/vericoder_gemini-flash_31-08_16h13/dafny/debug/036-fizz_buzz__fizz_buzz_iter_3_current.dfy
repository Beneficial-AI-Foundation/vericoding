

// <vc-helpers>
function sum_seq_func(s: seq<nat>): nat
{
  if |s| == 0 then 0 else s[0] + sum_seq_func(s[1..])
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
  var s: seq<nat> := [];
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == seq(i, k requires 0 <= k < i => (if k % 11 == 0 || k % 13 == 0 then count7_r(k) else 0))
  {
    if i % 11 == 0 || i % 13 == 0 {
      s := s + [count7_r(i)];
    } else {
      s := s + [0];
    }
    i := i + 1;
  }
  result := sum_seq_func(s);
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