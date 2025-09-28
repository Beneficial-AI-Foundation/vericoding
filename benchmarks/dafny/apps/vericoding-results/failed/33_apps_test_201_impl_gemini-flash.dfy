// <vc-preamble>
predicate ValidInput(C: int, Hr: int, Hb: int, Wr: int, Wb: int)
{
  C >= 0 && Hr > 0 && Hb > 0 && Wr > 0 && Wb > 0
}

predicate ValidCandyCombination(redCount: int, blueCount: int, C: int, Wr: int, Wb: int)
{
  redCount >= 0 && blueCount >= 0 && redCount * Wr + blueCount * Wb <= C
}

function Joy(redCount: int, blueCount: int, Hr: int, Hb: int): int
{
  redCount * Hr + blueCount * Hb
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `MaxJoyInRow` to ensure the `exists b` postcondition is met by returning the maximum joy for a given capacity. The previous recursive call to MaxJoyInRow was removed as the function can be directly calculated.*/
function MaxJoyInRow(C_remaining: int, current_red: int, Hb: int, Wb: int): int
    requires Wb > 0
    ensures forall b: int :: b >= 0 && b * Wb <= C_remaining ==> b * Hb <= MaxJoyInRow(C_remaining, current_red, Hb, Wb)
    ensures (C_remaining < Wb && MaxJoyInRow(C_remaining, current_red, Hb, Wb) == 0) || (C_remaining >= Wb && exists b: int :: b >= 0 && b * Wb <= C_remaining && b * Hb == MaxJoyInRow(C_remaining, current_red, Hb, Wb))
{
    if C_remaining < Wb then
        0
    else
        (C_remaining / Wb) * Hb
}
// </vc-helpers>

// <vc-spec>
method solve(C: int, Hr: int, Hb: int, Wr: int, Wb: int) returns (result: int)
  requires ValidInput(C, Hr, Hb, Wr, Wb)
  ensures result >= 0
  ensures exists redCount: int, blueCount: int :: 
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
    result == Joy(redCount, blueCount, Hr, Hb)
  ensures forall redCount: int, blueCount: int ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    Joy(redCount, blueCount, Hr, Hb) <= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adjusted the loop invariant for `maxJoy` to precisely track the maximum joy found so far for combinations of red and blue candies, up to the current `redCount`. This ensures that the postcondition `forall redCount, blueCount` can be proven more rigorously by leveraging the established invariants.*/
{
  var maxJoy: int := 0;

  var redCount: int := 0;
  while redCount * Wr <= C
    invariant redCount >= 0
    invariant maxJoy >= 0
    invariant forall r: int, b: int :: 0 <= r < redCount && 0 <= b && r * Wr + b * Wb <= C ==> Joy(r, b, Hr, Hb) <= maxJoy
    invariant forall r: int :: 0 <= r < redCount && r * Wr <= C ==> Joy(r, MaxJoyInRow(C - r * Wr, r, Hb, Wb) / Hb, Hr, Hb) <= maxJoy
  {
    var C_remaining := C - redCount * Wr;
    if C_remaining >= 0 {
      var currentJoy := redCount * Hr + MaxJoyInRow(C_remaining, redCount, Hb, Wb);
      if currentJoy > maxJoy {
        maxJoy := currentJoy;
      }
    }
    redCount := redCount + 1;
  }
  result := maxJoy;
}
// </vc-code>
