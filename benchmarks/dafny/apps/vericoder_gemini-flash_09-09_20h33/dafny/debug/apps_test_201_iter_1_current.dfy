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

    // We can't buy more red candies than C / Wr
    // We can't buy more blue candies than C / Wb
    // We also need to consider the case where Hr or Hb might be very small,
    // so it's possible to buy many candies with little joy per candy.
    // However, the number of candies is bounded by C / min(Wr, Wb)
    // If min(Wr, Wb) is 1, then the max number of candies is C.
    // So iterating up to C for each is safe.
    // The actual upper bound for redCount is C/Wr and for blueCount is C/Wb.
    // To ensure we don't iterate too many times for very small C/Wr values,
    // and correctly handle C=0, we use C/Wr + 1 and C/Wb + 1.
    // The +1 is to handle the case where C/Wr is 0, so we still iterate 0.
    // If C=0, redCount will go from 0 up to 0, and blueCount will go from 0 up to 0.

    var rLimit := C / Wr;
    var bLimit := C / Wb;

    // Small optimization: if Wr > C or Wb > C, then the corresponding limit is 0.
    // However, C/Wr will already handle this naturally if C < Wr.
    // In that case C/Wr = 0. So no explicit handling needed.


    // We iterate over possible counts of red candies.
    // The maximum possible red candies is C / Wr.
    // We need to iterate from 0 up to C/Wr.
    // The loop invariant ensures that maxJoy holds the maximum joy found so far.
    // The termination argument is straightforward.
    var redCount := 0;
    while redCount * Wr <= C
        invariant 0 <= redCount && redCount <= C / Wr + 1 // redCount can go up to C/Wr and then one more increment
        invariant forall rc: int, bc: int ::
                    0 <= rc && rc < redCount &&
                    ValidCandyCombination(rc, bc, C, Wr, Wb) ==> Joy(rc, bc, Hr, Hb) <= maxJoy
        invariant 0 <= maxJoy
        decreases (C / Wr + 1) - redCount
    {
        var remainingC := C - redCount * Wr;
        var blueCount := 0;
        // Iterate over possible counts of blue candies for the current redCount.
        // The maximum possible blue candies for the remaining budget is remainingC / Wb.
        while blueCount * Wb <= remainingC
            invariant 0 <= blueCount && blueCount <= remainingC / Wb + 1
            invariant forall bc': int ::
                        0 <= bc' && bc' < blueCount &&
                        ValidCandyCombination(redCount, bc', C, Wr, Wb) ==> Joy(redCount, bc', Hr, Hb) <= maxJoy
            invariant 0 <= maxJoy
            decreases (remainingC / Wb + 1) - blueCount
        {
            // Check if adding this combination is valid.
            // This is already guaranteed by the loop conditions:
            // redCount * Wr + blueCount * Wb <= redCount * Wr + remainingC = redCount * Wr + (C - redCount * Wr) = C
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

