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
lemma ValidCandyCombinationBounds(redCount: int, blueCount: int, C: int, Wr: int, Wb: int)
  requires ValidCandyCombination(redCount, blueCount, C, Wr, Wb)
  requires Wr > 0 && Wb > 0
  ensures redCount <= C / Wr
  ensures blueCount <= C / Wb
{
  calc {
    redCount * Wr;
    <= redCount * Wr + blueCount * Wb;
    <= C;
  }
  calc {
    blueCount * Wb;
    <= redCount * Wr + blueCount * Wb;
    <= C;
  }
}

lemma JoyLinear(redCount1: int, blueCount1: int, redCount2: int, blueCount2: int, Hr: int, Hb: int, k: int)
  requires Joy(redCount1, blueCount1, Hr, Hb) <= Joy(redCount2, blueCount2, Hr, Hb)
  ensures Joy(redCount1 + k, blueCount1 + k, Hr, Hb) <= Joy(redCount2 + k, blueCount2 + k,
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
lemma ValidCandyCombinationBounds(redCount: int, blueCount: int, C: int, Wr: int, Wb: int)
  requires ValidCandyCombination(redCount, blueCount, C, Wr, Wb)
  requires Wr > 0 && Wb > 0
  ensures redCount <= C / Wr
  ensures blueCount <= C / Wb
{
  calc {
    redCount * Wr;
    <= redCount * Wr + blueCount * Wb;
    <= C;
  }
  calc {
    blueCount * Wb;
    <= redCount * Wr + blueCount * Wb;
    <= C;
  }
}

lemma JoyLinear(redCount1: int, blueCount1: int, redCount2: int, blueCount2: int, Hr: int, Hb: int, k: int)
  requires Joy(redCount1, blueCount1, Hr, Hb) <= Joy(redCount2, blueCount2, Hr, Hb)
  ensures Joy(redCount1 + k, blueCount1 + k, Hr, Hb) <= Joy(redCount2 + k, blueCount2 + k,
// </vc-code>

