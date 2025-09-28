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
/* helper modified by LLM (iteration 3): add decreases clauses to fix termination errors */
function pow2_real(exp: int): real
  decreases if exp >= 0 then exp else -exp
{
  if exp == 0 then 1.0
  else if exp > 0 then 2.0 * pow2_real(exp - 1)
  else 0.5 * pow2_real(exp + 1)
}

/* helper modified by LLM (iteration 3): add decreases clauses to fix termination errors */
lemma pow2_real_pos(e: int)
  ensures pow2_real(e) > 0.0
  decreases if e >= 0 then e else -e
{
  if e > 0 { pow2_real_pos(e - 1); }
  else if e < 0 { pow2_real_pos(e + 1); }
}

lemma pow2_real_succ(e: int)
  ensures pow2_real(e + 1) == 2.0 * pow2_real(e)
{}

/* helper modified by LLM (iteration 3): add decreases clauses to fix termination errors */
lemma pow2_real_add(a: int, b: int)
  ensures pow2_real(a + b) == pow2_real(a) * pow2_real(b)
  decreases if b >= 0 then b else -b
{
  if b > 0 {
    pow2_real_add(a, b - 1);
  } else if b < 0 {
    pow2_real_add(a, b + 1);
  }
}

/* helper modified by LLM (iteration 3): add decreases clauses to fix termination errors */
lemma pow2_real_monotonic(a: int, b: int)
  ensures a < b ==> pow2_real(a) < pow2_real(b)
  decreases if b >= a then b - a else a - b
{
  if a < b {
    if b == a + 1 {
      pow2_real_succ(a);
      pow2_real_pos(a);
    } else {
      pow2_real_monotonic(a, b - 1);
      pow2_real_monotonic(b - 1, b);
    }
  }
}

lemma Pow2_real_equiv(n: nat)
  ensures Pow2(n) as real == pow2_real(n as int)
{
  if n > 0 {
    Pow2_real_equiv(n-1);
  }
}
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
  /* code modified by LLM (iteration 4): add lemma calls to prove postconditions */
  // Standard IEEE 754 double-precision float values
  var nmant: nat := 52;
  var nexp: nat := 11;
  var precision: nat := 15;
  var negep: int := -52;
  var maxexp: int := 1024;
  var minexp: int := -1022;

  // Prove positivity for various components
  pow2_real_pos(negep);                 // for info.eps > 0.0
  pow2_real_pos(negep - 1);           // for info.epsneg > 0.0
  pow2_real_pos(minexp);                // for info.tiny > 0.0
  pow2_real_pos(minexp - (nmant as int)); // for info.smallest_subnormal > 0.0
  
  var eps := pow2_real(negep);
  var epsneg := pow2_real(negep - 1);
  var tiny := pow2_real(minexp);
  var smallest_subnormal := pow2_real(minexp - (nmant as int));

  // Prove smallest_subnormal < tiny
  pow2_real_monotonic(minexp - (nmant as int), minexp);

  var max_val := (2.0 - pow2_real(-(nmant as int))) * pow2_real(maxexp - 1);
  
  // Prove info.max > 0.0
  pow2_real_monotonic(-(nmant as int), 1);
  assert pow2_real(1) == 2.0;
  pow2_real_pos(maxexp - 1);

  // Prove 'Pow2(info.maxexp as nat) as real > info.max'
  Pow2_real_equiv(maxexp as nat);
  pow2_real_succ(maxexp - 1);
  pow2_real_pos(-(nmant as int));

  var min_val := -max_val;

  info := FloatInfo(
      eps, epsneg, max_val, min_val, tiny, smallest_subnormal,
      maxexp, minexp, negep, nexp, nmant, precision
  );
}
// </vc-code>
