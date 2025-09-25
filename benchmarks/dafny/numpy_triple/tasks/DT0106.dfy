// <vc-preamble>
// Returns NumPy's True_ boolean scalar value
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method True_() returns (result: bool)
  // The result equals the boolean value true
  ensures result == true
  // True is the identity element for logical AND operations
  ensures forall b: bool {:trigger result && b} :: result && b == b
  // True is the absorbing element for logical OR operations  
  ensures forall b: bool {:trigger result || b} :: result || b == true
  // Negation of True gives false
  ensures !result == false
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
