// <vc-preamble>
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91;
// </vc-spec>
// <vc-code>
{
  var y1 := x;
  var y2 := 1;
  while (true)
    // the following two invariants are needed only to prove the postcondition
    invariant proveFunctionalPostcondition ==> 100 < x ==> y1 == x;
    invariant proveFunctionalPostcondition ==> x <= 100 < y1 && y2 == 1 ==> y1 == 101;
    // the following two lines justify termination, as in the paper by Katz and Manna
    invariant (y1 <= 111 && y2 >= 1) || (y1 == x && y2 == 1);
    decreases -2*y1 + 21*y2 + 2*(if x < 111 then 111 else x);
  {
    if (y1 > 100) {
      if (y2 == 1) {
        break;
      } else {
        y1 := y1 - 10;
        y2 := y2 - 1;
      }
    } else {
      y1 := y1 + 11;
      y2 := y2 + 1;
    }
  }
  z := y1 - 10;
}
// </vc-code>
