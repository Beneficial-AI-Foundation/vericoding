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
lemma Count7_R_Step(y: nat)
  ensures count7_r(y) == (if y % 10 == 7 then 1 else 0) + count7_r(y / 10)
{
  if y < 10 {
    assert y / 10 == 0;
    assert count7_r(y) == (if y % 10 == 7 then 1 else 0);
    assert count7_r(y / 10) == count7_r(0);
    assert count7_r(0) == 0;
  } else {
    assert count7_r(y) == (if y % 10 == 7 then 1 else 0) + count7_r(y / 10);
  }
}
// </vc-helpers>

// <vc-spec>
method count7(x: nat) returns (count: nat) 

  ensures count == count7_r(x)
// </vc-spec>
// <vc-code>
{
  var y := x;
  var c: nat := 0;
  while y > 0
    invariant c + count7_r(y) == count7_r(x)
    decreases y
  {
    Count7_R_Step(y);
    if y % 10 == 7 {
      c := c + 1;
    }
    y := y / 10;
  }
  count := c + count7_r(y);
}
// </vc-code>
