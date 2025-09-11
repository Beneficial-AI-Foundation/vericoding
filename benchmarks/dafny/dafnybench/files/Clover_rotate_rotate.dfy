// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method rotate(a: array<int>, offset:int) returns (b: array<int> )
  requires 0<=offset
  ensures b.Length==a.Length
  ensures forall  i::0<=i<a.Length ==>  b[i]==a[(i+offset)%a.Length]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
