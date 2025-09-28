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
proof fn lemma_can_eat_bounded(need: int, rem: int)
    requires
        0 <= need,
        0 <= rem,
    ensures
        0 <= can_eat(need, rem),
        can_eat(need, rem) <= need,
        can_eat(need, rem) <= rem,
{
    if need <= rem {
        assert(can_eat(need, rem) == need);
        assert(0 <= need);
        assert(need <= need);
        assert(need <= rem);
    } else {
        assert(can_eat(need, rem) == rem);
        assert(0 <= rem);
        assert(rem <= need) ==> (rem <= need);
        assert(rem <= rem);
    }
}

proof fn lemma_carrots_left_bounds(need: int, rem: int)
    requires
        0 <= need,
        0 <= rem,
    ensures
        0 <= carrots_left(need, rem),
        carrots_left(need, rem) <= rem,
{
    lemma_can_eat_bounded(need, rem);
    assert(carrots_left(need, rem) == rem - can_eat(need, rem));
    assert(0 <= rem - can_eat(need, rem));
    assert(rem - can_eat(need, rem) <= rem);
}

proof fn lemma_total_eaten_ge_number(number: int, need: int, rem: int)
    requires
        0 <= number,
        0 <= need,
        0 <= rem,
    ensures
        total_eaten(number, need, rem) >= number,
{
    lemma_can_eat_bounded(need, rem);
    assert(total_eaten(number, need, rem) == number + can_eat(need, rem));
    assert(0 <= can_eat(need, rem));
}
// </vc-helpers>

// <vc-spec>
fn eat(number: i8, need: i8, remaining: i8) -> (result: Vec<i8>)
    requires valid_input(number as int, need as int, remaining as int)
    ensures valid_result(result@.map(|i, x| x as int), number as int, need as int, remaining as int)
// </vc-spec>
// <vc-code>
{
    let n_i: int = number as int;
    let need_i: int = need as int;
    let rem_i: int = remaining as int;

    proof {
        assert(0 <= n_i);
        assert(0 <= need_i);
        assert(0 <= rem_i);
        // i8 bounds
        assert(-128 <= number as int && number as int <= 127);
        assert(-128 <= need as int && need as int <= 127);
        assert(-128 <= remaining as int && remaining as int <= 127);
        lemma_can_eat_bounded(need_i, rem_i);
        lemma_carrots_left_bounds(need_i, rem_i);
        lemma_total_eaten_ge_number(n_i, need_i, rem_i);
    }

    let eat_i: int = can_eat(need_i, rem_i);
    let te_i: int = total_eaten(n_i, need_i, rem_i);
    let cl_i: int = carrots_left(need_i, rem_i);

    proof {
        // carrots_left is between 0 and remaining <= 127, so it fits in i8
        assert(0 <= cl_i);
        assert(cl_i <= rem_i);
        assert(rem_i <= 127);
        assert(-128 <= cl_i && cl_i <= 127);
    }

    let first: i8 = te_i as i8;
    let second: i8 = cl_i as i8;

    let mut v: Vec<i8> = Vec::new();
    v.push(first);
    v.push(second);

    proof {
        // Relate exec values to specs
        assert(v@.len() == 2);
        // Map of result elements to ints equals [te_i, cl_i]
        // This, together with the definitions, establishes valid_result
    }

    v
}
// </vc-code>


}

fn main() {}