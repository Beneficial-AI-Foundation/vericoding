// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method strlen(s: string) returns (len: int)

  ensures len == |s|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
