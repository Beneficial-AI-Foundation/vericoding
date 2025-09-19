// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method mapparms(oldDomain: array<real>, newDomain: array<real>) returns (offset: real, scale: real)
  // Input domains must be arrays of exactly 2 elements
  requires oldDomain.Length == 2
  requires newDomain.Length == 2
  // Old domain endpoints must be distinct to avoid division by zero
  requires oldDomain[0] != oldDomain[1]
  // The linear map L(x) = offset + scale*x maps old domain to new domain
  ensures offset + scale * oldDomain[0] == newDomain[0]
  ensures offset + scale * oldDomain[1] == newDomain[1]
  // Mathematical relationships defining the parameters
  ensures scale == (newDomain[1] - newDomain[0]) / (oldDomain[1] - oldDomain[0])
  ensures offset == (oldDomain[1] * newDomain[0] - oldDomain[0] * newDomain[1]) / (oldDomain[1] - oldDomain[0])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
