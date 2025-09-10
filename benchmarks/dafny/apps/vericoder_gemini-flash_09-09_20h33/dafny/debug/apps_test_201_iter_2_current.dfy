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

// <vc-helpers>
function max(a: int, b: int): int {
  if a > b then a else b
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
{
    var maxJoy := 0;

    var rLimit := C / Wr;
    var bLimit := C / Wb;

    var redCount := 0;
    while redCount * Wr <= C
        invariant 0 <= redCount
        invariant forall rc: int, bc: int ::
                    0 <= rc && rc < redCount &&
                    ValidCandyCombination(rc, bc, C, Wr, Wb) ==> Joy(rc, bc, Hr, Hb) <= maxJoy
        invariant 0 <= maxJoy
        decreases (C / Wr + 1) - redCount
    {
        var remainingC := C - redCount * Wr;
        var blueCount := 0;
        while blueCount * Wb <= remainingC
            invariant 0 <= blueCount
            invariant forall bc': int ::
                        0 <= bc' && bc' < blueCount &&
                        ValidCandyCombination(redCount, bc', C, Wr, Wb) ==> Joy(redCount, bc', Hr, Hb) <= maxJoy
            invariant 0 <= maxJoy
            decreases (remainingC / Wb + 1) - blueCount
        {
            assert ValidCandyCombination(redCount, blueCount, C, Wr, Wb);
            var currentJoy := Joy(redCount, blueCount, Hr, Hb);
            maxJoy := max(maxJoy, currentJoy);

            blueCount := blueCount + 1;
        }
        redCount := redCount + 1;
    }
    result := maxJoy;
}
// </vc-code>

