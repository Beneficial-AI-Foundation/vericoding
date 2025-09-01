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
lemma count7_loop_invariant(x: nat, temp: nat, count: nat)
  requires temp == x / pow10(count)
  requires count7_r(x) == count7_r(temp) + count
  ensures count7_r(x) == count7_r(temp) + count
{
}

function pow10(n: nat): nat
  ensures pow10(n) > 0
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

lemma count7_decomposition(x: nat)
  requires x >= 10
  ensures count7_r(x) == (if x % 10 == 7 then 1 else 0) + count7_r(x / 10)
{
}

lemma count7_base_case(x: nat)
  requires x < 10
  ensures count7_r(x) == (if x == 7 then 1 else 0)
{
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
  count := 0;
  var temp := x;
  
  while temp > 0
    invariant count7_r(x) == count7_r(temp) + count
    decreases temp
  {
    if temp % 10 == 7 {
      count := count + 1;
    }
    temp := temp / 10;
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