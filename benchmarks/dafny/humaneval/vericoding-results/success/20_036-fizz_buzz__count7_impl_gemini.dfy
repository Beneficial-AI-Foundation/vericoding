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

// </vc-helpers>

// <vc-spec>
method count7(x: nat) returns (count: nat) 

  ensures count == count7_r(x)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): removed semicolon from invariant clause */
  count := 0;
  var temp_x := x;
  while temp_x > 0
    invariant count + count7_r(temp_x) == count7_r(x)
  {
    if temp_x % 10 == 7 {
      count := count + 1;
    }
    temp_x := temp_x / 10;
  }
}
// </vc-code>
