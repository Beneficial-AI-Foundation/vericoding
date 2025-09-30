// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method polyder(poly: array<real>, m: int) returns (result: array<real>)
    requires 
        m > 0 &&
        m <= poly.Length
    ensures 
        result.Length == poly.Length - m
// </vc-spec>
// <vc-code>
{
  if m == poly.Length {
    result := new real[0];
  } else {
    result := new real[poly.Length - m];
    var i := 0;
    while i < result.Length
      invariant 0 <= i <= result.Length
      invariant forall k :: 0 <= k < i ==> result[k] == poly[k + m]
    {
      result[i] := poly[i + m];
      i := i + 1;
    }
  }
}
// </vc-code>
