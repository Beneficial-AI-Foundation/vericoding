// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(number: int, need: int, remaining: int) -> bool
{
    0 <= number <= 1000 && 0 <= need <= 1000 && 0 <= remaining <= 1000
}

spec fn can_eat(need: int, remaining: int) -> int
{
    if need <= remaining { need } else { remaining }
}

spec fn total_eaten(number: int, need: int, remaining: int) -> int
{
    number + can_eat(need, remaining)
}

spec fn carrots_left(need: int, remaining: int) -> int
{
    remaining - can_eat(need, remaining)
}

spec fn valid_result(result: Seq<int>, number: int, need: int, remaining: int) -> bool
{
    result.len() == 2 &&
    result[0] == total_eaten(number, need, remaining) &&
    result[1] == carrots_left(need, remaining) &&
    result[0] >= number &&
    result[1] >= 0 &&
    result[1] <= remaining
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No helpers are needed as the specification contains a contradiction. */

// </vc-helpers>

// <vc-spec>
fn eat(number: i8, need: i8, remaining: i8) -> (result: Vec<i8>)
    requires valid_input(number as int, need as int, remaining as int)
    ensures valid_result(result@.map(|i, x| x as int), number as int, need as int, remaining as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Correctly calculate values and prove the valid part of the spec. The overflow part is impossible to satisfy. */
    let eaten_now = if need <= remaining {
        need
    } else {
        remaining
    };

    // new_remaining is guaranteed to be in the i8 range.
    let new_remaining = remaining - eaten_now;

    // Use a wider type for the sum, as number + eaten_now can exceed 127.
    let new_total_wide: i32 = (number as i32) + (eaten_now as i32);

    proof {
        let n = number as int;
        let d = need as int;
        let r = remaining as int;
        // Prove the parts of the postcondition that are satisfiable.
        assert(new_remaining as int == carrots_left(d, r));
        assert(new_total_wide as int == total_eaten(n, d, r));
        assert(total_eaten(n, d, r) >= n);
        assert(carrots_left(d, r) >= 0);
        assert(carrots_left(d, r) <= r);
    }

    // This cast is not provably safe. `new_total_wide` can be up to 254, which overflows i8.
    // Verus fails here, as it cannot prove that `new_total as int == new_total_wide as int`.
    // This is the root cause of the postcondition failure.
    // The function spec is contradictory and cannot be implemented with the given types.
    let new_total = new_total_wide as i8;

    let result = vec![new_total, new_remaining];
    result
}
// </vc-code>


}

fn main() {}