// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
  n >= 1
}

spec fn power(base: int, exp: int) -> int
  decreases exp when exp >= 0
{
  if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn count_starts_with_1(n: int) -> int {
  power(10, n - 1)
}

spec fn count_ends_with_1(n: int) -> int {
  if n == 1 { 1 } else { 9 * power(10, n - 2) }
}

spec fn count_starts_and_ends_with_1(n: int) -> int {
  if n <= 2 { 1 } else { power(10, n - 2) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma to provide complete proof of the final formula */
proof fn lemma_count_formula_equivalence(n: int)
    requires
        n >= 1,
    ensures
        count_starts_with_1(n) + count_ends_with_1(n) - count_starts_and_ends_with_1(n) == (
            if n >= 2 {
                power(10, n - 1) + 8 * power(10, n - 2)
            } else {
                1
            }
        )
{
    if n == 1 {
        assert(count_starts_with_1(1) == 1);
        assert(count_ends_with_1(1) == 1);
        assert(count_starts_and_ends_with_1(1) == 1);
    } else {
        assert(count_starts_with_1(n) == power(10, n - 1));
        assert(count_ends_with_1(n) == 9 * power(10, n - 2));
        assert(count_starts_and_ends_with_1(n) == power(10, n - 2));
        assert(count_starts_with_1(n) + count_ends_with_1(n) - count_starts_and_ends_with_1(n) == 
               power(10, n - 1) + 9 * power(10, n - 2) - power(10, n - 2));
        assert(power(10, n - 1) + 9 * power(10, n - 2) - power(10, n - 2) == 
               power(10, n - 1) + 8 * power(10, n - 2));
    }
}
// </vc-helpers>

// <vc-spec>
fn starts_one_ends(n: i8) -> (result: i8)
  requires 
    valid_input(n as int)
  ensures 
    result as int == count_starts_with_1(n as int) + count_ends_with_1(n as int) - count_starts_and_ends_with_1(n as int),
    result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer operations to avoid ghost types in exec code */
    proof {
        lemma_count_formula_equivalence(n as int);
    }
    
    if n == 1 {
        1i8
    } else {
        let power1 = 10i8.pow((n - 1) as u32);
        let power2 = 10i8.pow((n - 2) as u32);
        let total = power1 + 8 * power2;
        assert(total >= 0);
        total
    }
}
// </vc-code>


}

fn main() {}