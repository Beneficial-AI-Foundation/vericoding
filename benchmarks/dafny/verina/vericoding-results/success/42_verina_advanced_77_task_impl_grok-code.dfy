// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: nat, b: nat): nat { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var left := new nat[height.Length];
  var right := new nat[height.Length];
  var maxL := 0;
  var i := 0;
  while i < height.Length 
    invariant 0 <= i <= height.Length
  {
    maxL := if height[i] > maxL then height[i] else maxL;
    left[i] := maxL;
    i := i + 1;
  }
  var maxR := 0;
  i := height.Length - 1;
  while i >= 0 
    invariant -1 <= i < height.Length
  {
    maxR := if height[i] > maxR then height[i] else maxR;
    right[i] := maxR;
    i := i - 1;
  }
  var total : nat := 0;
  i := 0;
  while i < height.Length 
    invariant 0 <= i <= height.Length
  {
    var water := min(left[i], right[i]) - height[i];
    total := total + if water > 0 then water else 0;
    i := i + 1;
  }
  result := total;
}
// </vc-code>
