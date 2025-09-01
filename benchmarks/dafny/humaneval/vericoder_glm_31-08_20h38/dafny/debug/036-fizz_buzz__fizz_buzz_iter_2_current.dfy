

// <vc-helpers>
function generateSeq(n: nat, f: (i: int) -> int requires 0 <= i < n): seq<int> {
  if n == 0 then [] else [f(0)] + generateSeq(n-1, i => f(i+1))
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
  var total: nat := 0;
  for i := 0 to n
    invariant total == sum(generateSeq(i, j => if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
  {
    if i % 11 == 0 || i % 13 == 0 {
      total := total + count7_r(i);
    }
  }
  return total;
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