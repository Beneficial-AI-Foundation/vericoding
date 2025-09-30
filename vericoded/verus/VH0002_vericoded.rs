// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(number: int) -> bool {
    number >= 0
}

spec fn valid_output(result: int, input: int) -> bool {
    0 <= result < 1 && result == input - floor_spec(input)
}

spec fn floor_spec(x: int) -> int {
    if x >= 0 {
        floor_nonnegative(x)
    } else {
        -ceil_nonnegative(-x)
    }
}

spec fn floor_nonnegative(x: int) -> int {
    floor_helper(x, 0)
}

spec fn floor_helper(x: int, n: int) -> int 
    decreases x when x >= 0 && n >= 0
{
    if x < 1 { 
        n
    } else { 
        floor_helper(x - 1, n + 1)
    }
}

spec fn ceil_nonnegative(x: int) -> int {
    if x == 0 { 
        0
    } else if floor_nonnegative(x) == x {
        x
    } else {
        floor_nonnegative(x) + 1
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_floor_helper_add(y: int, n: int)
    requires
        y >= 0,
        n >= 0,
    ensures
        floor_helper(y, n) == n + floor_helper(y, 0),
    decreases y
{
    if y < 1 {
        assert(floor_helper(y, n) == n);
        assert(floor_helper(y, 0) == 0);
    } else {
        lemma_floor_helper_add(y - 1, n + 1);
        lemma_floor_helper_add(y - 1, 1);
        assert(floor_helper(y, n) == floor_helper(y - 1, n + 1));
        assert(floor_helper(y, 0) == floor_helper(y - 1, 1));
        assert(floor_helper(y - 1, n + 1) == (n + 1) + floor_helper(y - 1, 0));
        assert(floor_helper(y - 1, 1) == 1 + floor_helper(y - 1, 0));
        assert(n + floor_helper(y, 0) == n + (1 + floor_helper(y - 1, 0)));
        assert(n + (1 + floor_helper(y - 1, 0)) == (n + 1) + floor_helper(y - 1, 0));
        assert((n + 1) + floor_helper(y - 1, 0) == floor_helper(y - 1, n + 1));
    }
}

proof fn lemma_floor_helper_zero_id(y: int)
    requires
        y >= 0,
    ensures
        floor_helper(y, 0) == y,
    decreases y
{
    if y < 1 {
        assert(y == 0);
        assert(floor_helper(y, 0) == 0);
    } else {
        lemma_floor_helper_zero_id(y - 1);
        lemma_floor_helper_add(y - 1, 1);
        assert(floor_helper(y, 0) == floor_helper(y - 1, 1));
        assert(floor_helper(y - 1, 1) == 1 + floor_helper(y - 1, 0));
        assert(floor_helper(y - 1, 0) == y - 1);
        assert(floor_helper(y, 0) == 1 + (y - 1));
        assert(floor_helper(y, 0) == y);
    }
}

proof fn lemma_floor_nonnegative_id(x: int)
    requires
        x >= 0,
    ensures
        floor_nonnegative(x) == x,
{
    lemma_floor_helper_zero_id(x);
    assert(floor_nonnegative(x) == floor_helper(x, 0));
    assert(floor_helper(x, 0) == x);
}

proof fn lemma_ceil_nonnegative_id(x: int)
    requires
        x >= 0,
    ensures
        ceil_nonnegative(x) == x,
{
    if x == 0 {
        assert(ceil_nonnegative(x) == 0);
    } else {
        lemma_floor_nonnegative_id(x);
        assert(floor_nonnegative(x) == x);
        assert(ceil_nonnegative(x) == x);
    }
}

proof fn lemma_floor_spec_id(x: int)
    ensures
        floor_spec(x) == x,
{
    if x >= 0 {
        lemma_floor_nonnegative_id(x);
        assert(floor_spec(x) == floor_nonnegative(x));
        assert(floor_spec(x) == x);
    } else {
        let y = -x;
        assert(y >= 0);
        lemma_ceil_nonnegative_id(y);
        assert(floor_spec(x) == -ceil_nonnegative(-x));
        assert(floor_spec(x) == -y);
        assert(-y == x);
    }
}
// </vc-helpers>

// <vc-spec>
fn truncate_number(number: i8) -> (result: i8)
    requires valid_input(number as int)
    ensures valid_output(result as int, number as int)
// </vc-spec>
// <vc-code>
{
    let result: i8 = 0i8;
    proof {
        lemma_floor_spec_id(number as int);
    }
    assert((result as int) >= 0);
    assert((result as int) < 1);
    result
}
// </vc-code>


}

fn main() {}