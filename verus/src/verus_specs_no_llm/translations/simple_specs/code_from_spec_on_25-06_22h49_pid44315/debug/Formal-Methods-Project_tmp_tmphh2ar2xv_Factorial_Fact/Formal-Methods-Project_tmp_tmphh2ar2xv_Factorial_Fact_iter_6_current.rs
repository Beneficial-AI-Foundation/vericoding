use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fact_spec(x: int) -> int
    decreases x
{
    if x <= 0 {
        1
    } else {
        x * fact_spec(x - 1)
    }
}

fn Fact(x: int) -> (y: int)
    requires
        x >= 0
    ensures
        y == fact_spec(x),
        y >= 1
    decreases x
{
    if x <= 0 {
        1
    } else {
        let prev = Fact(x - 1);
        assert(prev == fact_spec(x - 1));
        assert(prev >= 1);
        assert(x >= 1);
        let result = x * prev;
        assert(result == x * fact_spec(x - 1));
        assert(result == fact_spec(x)) by {
            // The definition of fact_spec(x) when x > 0
            assert(fact_spec(x) == x * fact_spec(x - 1));
        };
        assert(result >= 1) by {
            // Since x >= 1 and prev >= 1, their product is >= 1
            assert(x >= 1);
            assert(prev >= 1);
            // For positive integers, if a >= 1 and b >= 1, then a * b >= 1
            assert(x * prev >= 1);
        };
        result
    }
}

}