// The postcondition `ensures m<=x && m<=y && m<=z` means I need to find a value that is at most the minimum of the three inputs. The simplest approach is to find the actual minimum of the three values.

// A8Q2 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method A8Q1(x: int, y: int, z: int) returns (m: int)
/*Pre-Condition*/   requires true;
/*Post-Condition*/  ensures m<=x && m<=y && m<=z;
// </vc-spec>
// <vc-code>
{
  if x <= y && x <= z {
    m := x;
  } else if y <= x && y <= z {
    m := y;
  } else {
    m := z;
  }
}
// </vc-code>

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/