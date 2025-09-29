// <vc-preamble>
// Structure representing floating point type information returned by numpy.finfo
datatype FloatInfo = FloatInfo(
    bits: nat,                    // The number of bits occupied by the type
    eps: real,                    // The smallest representable positive number such that 1.0 + eps != 1.0
    max: real,                    // The largest representable number
    min: real,                    // The smallest representable number, typically -max
    precision: nat,               // The approximate number of decimal digits to which this kind of float is precise
    resolution: real,             // The approximate decimal resolution of this type
    smallest_normal: real,        // The smallest positive floating point number with 1 as leading bit in the mantissa
    smallest_subnormal: real      // The smallest positive floating point number with 0 as leading bit in the mantissa
)

// Returns floating point type information with mathematically consistent properties
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_finfo() returns (info: FloatInfo)
    // Basic sanity checks
    ensures info.bits > 0
    ensures info.precision > 0
    // eps is positive and small
    ensures info.eps > 0.0 && info.eps < 1.0
    // max is positive, min is negative
    ensures info.max > 0.0 && info.min < 0.0
    // min is typically -max for symmetric floating point types
    ensures info.min == -info.max
    // resolution is positive
    ensures info.resolution > 0.0
    // smallest_normal is positive and smaller than 1
    ensures info.smallest_normal > 0.0 && info.smallest_normal < 1.0
    // smallest_subnormal is positive and smaller than or equal to smallest_normal
    ensures info.smallest_subnormal > 0.0 && info.smallest_subnormal <= info.smallest_normal
    // eps represents the machine epsilon property
    ensures info.eps == info.resolution
    // The number of bits should be reasonable (32 or 64 for common float types)
    ensures info.bits == 32 || info.bits == 64
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed scientific notation syntax errors by using decimal format */
  // Use float64 (double precision) parameters
  var bits := 64;
  var eps := 0.0000000000000002220446049250313;
  var max := 179769313486231570000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0;
  var min := -179769313486231570000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0;
  var precision := 15;
  var resolution := 0.0000000000000002220446049250313;
  var smallest_normal := 0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002225073858507201;
  var smallest_subnormal := 0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005;
  
  info := FloatInfo(
    bits := bits,
    eps := eps,
    max := max,
    min := min,
    precision := precision,
    resolution := resolution,
    smallest_normal := smallest_normal,
    smallest_subnormal := smallest_subnormal
  );
}
// </vc-code>
