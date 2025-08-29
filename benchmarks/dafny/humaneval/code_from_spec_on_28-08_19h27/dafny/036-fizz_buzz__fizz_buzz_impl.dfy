// <vc-helpers>
function fizz_buzz_r(n: nat): nat {
  if n == 0 then 0
  else (
    var count := fizz_buzz_r(n - 1);
    if n % 15 == 0 then count + 1
    else if n % 3 == 0 then count + 1  
    else if n % 5 == 0 then count + 1
    else count
  )
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method fizz_buzz(n: nat) returns (result: nat)
Process input. Requires: returns the correct size/count. Ensures: returns the correct value.
*/
// </vc-description>

// <vc-spec>
method fizz_buzz(n: nat) returns (result: nat)
  ensures result == fizz_buzz_r(n)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 1;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant result == fizz_buzz_r(i - 1)
  {
    if i % 15 == 0 || i % 3 == 0 || i % 5 == 0 {
      result := result + 1;
    }
    i := i + 1;
  }
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