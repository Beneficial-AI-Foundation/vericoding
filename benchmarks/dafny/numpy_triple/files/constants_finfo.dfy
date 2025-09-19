// <vc-preamble>
// Structure representing floating-point type information
datatype FloatInfo = FloatInfo(
  eps: real,                    // Machine epsilon
  epsneg: real,                // Negative machine epsilon  
  max: real,                   // Maximum representable value
  min: real,                   // Minimum representable value (typically -max)
  tiny: real,                  // Smallest positive normal number
  smallest_subnormal: real,    // Smallest positive subnormal number
  maxexp: int,                 // Maximum exponent
  minexp: int,                 // Minimum exponent
  negep: int,                  // Negative epsilon exponent
  nexp: nat,                   // Number of bits in exponent
  nmant: nat,                  // Number of bits in mantissa
  precision: nat               // Approximate decimal precision
)

// Function to compute integer power of 2
function Pow2(exp: nat): nat
{
  if exp == 0 then 1
  else 2 * Pow2(exp - 1)
}

// Returns machine limits for floating point types
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_finfo() returns (info: FloatInfo)
  ensures info.eps > 0.0
  ensures info.epsneg > 0.0
  // eps represents the gap from 1.0 to next larger float
  ensures 1.0 + info.eps > 1.0
  // epsneg represents the gap from 1.0 to next smaller float  
  ensures 1.0 - info.epsneg < 1.0
  // Max is positive and finite
  ensures info.max > 0.0
  // Min is negative max (for symmetric representation)
  ensures info.min == -info.max
  // Tiny (smallest normal) is positive
  ensures info.tiny > 0.0
  // Smallest subnormal is positive and less than tiny
  ensures info.smallest_subnormal > 0.0
  ensures info.smallest_subnormal < info.tiny
  // Exponent relationships - maxexp must be positive for safe casting
  ensures info.maxexp > 0
  ensures info.minexp < 0
  ensures info.negep < 0
  // Bit counts are positive
  ensures info.nexp > 0
  ensures info.nmant > 0
  // Precision is at least 1
  ensures info.precision >= 1
  // Relationship between max value and maxexp (2^maxexp causes overflow)
  ensures Pow2(info.maxexp as nat) as real > info.max
  // Relationship between mantissa bits and precision
  ensures info.precision <= info.nmant
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
