// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow(base: int, exp: int) -> int
  decreases exp
{
  if exp <= 0 { 1 }
  else { base * pow(base, exp - 1) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes to helpers since the last iteration, as errors were in the main code block. */
proof fn pow_properties_for_positive_bases_and_exponents(base: int, exp: int)
  requires
      base > 0,
      exp >= 0,
  ensures
      pow(base, exp) > 0
{
  if exp == 0 {
    assert(pow(base, exp) == 1);
  } else {
    pow_properties_for_positive_bases_and_exponents(base, exp - 1);
    assert(pow(base, exp) == base * pow(base, exp - 1));
    assert(base > 0 && pow(base, exp - 1) > 0);
  }
}

proof fn pow_monotonic_exp(base: int, exp1: int, exp2: int)
  requires
      base > 0,
      exp1 >= 0,
      exp2 >= 0,
      exp1 < exp2,
  ensures
      pow(base, exp1) < pow(base, exp2)
{
  if exp1 + 1 == exp2 {
    pow_properties_for_positive_bases_and_exponents(base, exp1);
    assert(pow(base, exp2) == base * pow(base, exp1));
    assert(base > 0);
    assert(pow(base, exp1) > 0);
    assert(pow(base, exp2) > pow(base, exp1));
  } else {
    pow_monotonic_exp(base, exp1, exp2 - 1);
    pow_properties_for_positive_bases_and_exponents(base, exp1);
    pow_properties_for_positive_bases_and_exponents(base, exp2 - 1);
    assert(base > 0);
    assert(pow(base, exp2 - 1) > 0);
    assert(pow(base, exp2) == base * pow(base, exp2 - 1));
    assert(pow(base, exp2) > pow(base, exp2 - 1));
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (years: i8)
  requires 
      1 <= a <= b <= 10,
      forall|base: int, exp: int| exp >= 0 ==> (
          (exp == 0 ==> pow(base, exp) == 1) &&
          (exp > 0 && base > 0 ==> pow(base, exp) > 0) &&
          (exp > 0 && base == 0 ==> pow(base, exp) == 0)
      ),
  ensures 
      years >= 0,
      (a as int) * pow(3, years as int) > (b as int) * pow(2, years as int),
      years == 0 || (a as int) * pow(3, (years - 1) as int) <= (b as int) * pow(2, (years - 1) as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Cast `years` to `i64` before using it in the `pow` function, as `pow` expects `int`, and `years` is `i8`. The issue was that `years as int` was being used in a non-ghost context, which is not allowed. Casting to `i64` resolves this by effectively converting it before it's interpreted as `int` by `pow`. */
{
  let mut years: i8 = 0;

  while (a as i64) * (pow(3, years as i64) as i64) <= (b as i64) * (pow(2, years as i64) as i64)
    invariant
        years >= 0,
        (years as int) <= 100 // Reasonable upper bound to prevent overflow during proof search
    decreases 100 - years
  {
    // Proof to show that pow(3, years) and pow(2, years) are positive
    proof {
      pow_properties_for_positive_bases_and_exponents(3, years as int);
      pow_properties_for_positive_bases_and_exponents(2, years as int);
    }
    years = years + 1;
    
  }
  years
}
// </vc-code>


}

fn main() {}