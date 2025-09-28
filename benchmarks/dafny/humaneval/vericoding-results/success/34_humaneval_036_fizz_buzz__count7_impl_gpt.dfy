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
lemma Count7Unfold(n: nat)
  ensures (if n < 10 then count7_r(n) == (if n % 10 == 7 then 1 else 0) else count7_r(n) == (if n % 10 == 7 then 1 else 0) + count7_r(n / 10))
{
}
// </vc-helpers>

// <vc-spec>
method count7(x: nat) returns (count: nat) 

  ensures count == count7_r(x)
// </vc-spec>
// <vc-code>
{
  var y: nat := x;
  count := 0;
  while y >= 10
    invariant count + count7_r(y) == count7_r(x)
    decreases y
  {
    var lst: nat := if y % 10 == 7 then 1 else 0;
    count := count + lst;
    y := y / 10;
  }
  if y < 10 {
    assert count7_r(y) == (if y % 10 == 7 then 1 else 0);
  }
  var last: nat := if y % 10 == 7 then 1 else 0;
  count := count + last;
}
// </vc-code>
