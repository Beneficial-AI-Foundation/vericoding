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
/* helper modified by LLM (iteration 5): no changes from previous iteration, helper is correct */
proof fn lemma_bound(a: int, b: int)
    requires
        1 <= a <= b <= 10,
        a * pow(3, 6) <= b * pow(2, 6),
    ensures false
{
    assert(pow(3, 6) == 729) by(compute);
    assert(pow(2, 6) == 64) by(compute);

    assert(a * 729 <= b * 64); // from requires

    assert(a >= 1);
    assert(a * 729 >= 729);

    assert(b <= 10);
    assert(b * 64 <= 640);

    // From the assertions above, we have this chain:
    // 729 <= a * 729 <= b * 64 <= 640
    // This implies 729 <= 640, which is a contradiction.
    assert(false);
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
    /* code modified by LLM (iteration 5): cast to int in loop condition to avoid overflow checks */
    let mut years: i8 = 0;
    let mut p3: i32 = 1;
    let mut p2: i32 = 1;

    while (a as int) * (p3 as int) <= (b as int) * (p2 as int)
        invariant
            1 <= a <= b <= 10,
            0 <= years <= 6,
            p3 == pow(3, years as int),
            p2 == pow(2, years as int),
            years == 0 || (a as int) * pow(3, (years - 1) as int) <= (b as int) * pow(2, (years - 1) as int),
        decreases 7 - years
    {
        proof {
            if years == 6 {
                lemma_bound(a as int, b as int);
            }
        }

        p3 = p3 * 3;
        p2 = p2 * 2;
        years = years + 1;
    }

    years
}
// </vc-code>


}

fn main() {}