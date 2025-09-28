// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(train_fare: int, bus_fare: int) -> bool {
    1 <= train_fare <= 100 && 1 <= bus_fare <= 100 && bus_fare % 2 == 0
}

spec fn total_cost(train_fare: int, bus_fare: int) -> int
    recommends valid_input(train_fare, bus_fare)
{
    train_fare + bus_fare / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): arithmetic facts for even numbers and division by 2, and total_cost bounds under valid_input */
proof fn lemma_even_div2_properties(b: int)
    requires
        1int <= b,
        b <= 100int,
        b % 2int == 0int,
    ensures
        0int <= b/2int,
        b/2int <= 50int,
        2int * (b/2int) == b,
{
    assert(b == 2int * (b / 2int) + b % 2int);
    assert(b % 2int == 0int);
    assert(2int * (b / 2int) == b);
    assert(0int <= b / 2int);
    assert(b / 2int <= 50int);
}

/* helper modified by LLM (iteration 5): bounds on total_cost under valid_input */
proof fn lemma_total_cost_bounds(t: int, b: int)
    requires
        valid_input(t, b),
    ensures
        2int <= total_cost(t, b),
        total_cost(t, b) <= 150int,
{
    assert(1int <= t);
    assert(t <= 100int);
    assert(1int <= b);
    assert(b <= 100int);
    assert(b % 2int == 0int);
    lemma_even_div2_properties(b);
    if b <= 1int {
        assert(b == 1int);
        assert(1int % 2int == 1int);
        assert(false);
    }
    assert(2int <= b);
    assert(1int <= b / 2int);
    assert(total_cost(t, b) == t + b / 2int);
    assert(2int <= total_cost(t, b));
    assert(total_cost(t, b) <= 150int);
}
// </vc-helpers>

// <vc-spec>
fn solve(train_fare: i8, bus_fare: i8) -> (result: i8)
    requires valid_input(train_fare as int, bus_fare as int)
    ensures result as int == total_cost(train_fare as int, bus_fare as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute in mathematical ints (and wider machine ints) to avoid i8 overflow; connect to spec */
    let t: int = train_fare as int;
    let b: int = bus_fare as int;

    proof {
        assert(valid_input(t, b));
        lemma_total_cost_bounds(t, b);
    }

    let total: int = total_cost(t, b);

    // Perform the arithmetic using a wider machine integer to avoid i8 overflow
    let res16: i16 = (train_fare as i16) + ((bus_fare as i16) / 2i16);
    let result_val: i8 = res16 as i8;

    proof {
        // Bridge between machine ints and mathematical ints
        assert(((bus_fare as i16) / 2i16) as int == b / 2int);
        assert((train_fare as i16) as int == t);
        assert((res16) as int == t + b / 2int);
        assert(total == t + b / 2int);
        // Therefore, result as int equals total
        assert((result_val as int) == total);
    }

    result_val
}
// </vc-code>


}

fn main() {}