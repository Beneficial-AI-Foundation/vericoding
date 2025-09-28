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
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing duplicate lemma keyword */
proof fn lemma_pow_monotonic(base: int, exp1: int, exp2: int)
    requires base > 1, exp1 >= 0, exp2 >= exp1
    ensures pow(base, exp2) >= pow(base, exp1)
    decreases exp2 - exp1
{
    if exp2 == exp1 {
    } else {
        lemma_pow_monotonic(base, exp1, exp2 - 1);
    }
}

proof fn lemma_pow_positive(base: int, exp: int)
    requires base > 0, exp >= 0
    ensures pow(base, exp) > 0
    decreases exp
{
    if exp == 0 {
    } else {
        lemma_pow_positive(base, exp - 1);
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
{
    /* code modified by LLM (iteration 5): moved pow calculations to ghost variables to fix compilation error */
    let mut years: i8 = 0;
    
    while years < 100
        invariant
            years >= 0,
            years < 100,
            forall|y: int| 0 <= y < years ==> (a as int) * pow(3, y) <= (b as int) * pow(2, y),
        decreases 100 - years
    {
        proof {
            lemma_pow_positive(3, years as int);
            lemma_pow_positive(2, years as int);
            
            let ghost a_power = (a as int) * pow(3, years as int);
            let ghost b_power = (b as int) * pow(2, years as int);
            
            if a_power > b_power {
                return years;
            }
        }
        
        years = years + 1;
    }
    
    years
}
// </vc-code>


}

fn main() {}