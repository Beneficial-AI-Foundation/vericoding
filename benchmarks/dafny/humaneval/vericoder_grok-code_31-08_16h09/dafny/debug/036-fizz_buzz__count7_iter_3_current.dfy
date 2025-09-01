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
method fizz_buzz(n: nat) returns (result: nat)
  ensures result == sum(seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0)))
{
  result := 0;
  for i : nat := 0 to n
    invariant 0 <= i <= n
    invariant result == sum(seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)))
  {
    if i % 11 == 0 || i % 13 == 0 {
      result := result + count7_r(i);
    }
  }
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
  if x == 0 {
    count := 0;
  } else {
    var rec := count7(x / 10);
    count := rec + (if x % 10 == 7 then 1 else 0);
  }
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