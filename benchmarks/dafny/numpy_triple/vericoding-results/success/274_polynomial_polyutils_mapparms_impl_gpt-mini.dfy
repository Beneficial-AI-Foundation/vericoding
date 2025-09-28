// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): proves that the computed offset and scale map old endpoints to new endpoints */
lemma MapParamsAlgebra(old0: real, old1: real, new0: real, new1: real)
  requires old0 != old1
  ensures ((old1*new0 - old0*new1)/(old1 - old0)) + ((new1 - new0)/(old1 - old0))*old0 == new0
  ensures ((old1*new0 - old0*new1)/(old1 - old0)) + ((new1 - new0)/(old1 - old0))*old1 == new1
{
  var denom := old1 - old0;
  calc {
    ((old1*new0 - old0*new1)/denom) + ((new1 - new0)/denom)*old0;
    == { }
    (old1*new0 - old0*new1 + old0*(new1 - new0)) / denom;
    == { }
    ((old1 - old0)*new0) / denom;
    == { }
    new0;
  }
  calc {
    ((old1*new0 - old0*new1)/denom) + ((new1 - new0)/denom)*old1;
    == { }
    (old1*new0 - old0*new1 + old1*(new1 - new0)) / denom;
    == { }
    ((old1 - old0)*new1) / denom;
    == { }
    new1;
  }
}

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
  /* code modified by LLM (iteration 2): compute scale and offset and invoke helper to discharge equalities */
  scale := (newDomain[1] - newDomain[0]) / (oldDomain[1] - oldDomain[0]);
  offset := (oldDomain[1] * newDomain[0] - oldDomain[0] * newDomain[1]) / (oldDomain[1] - oldDomain[0]);
  MapParamsAlgebra(oldDomain[0], oldDomain[1], newDomain[0], newDomain[1]);
}

// </vc-code>
