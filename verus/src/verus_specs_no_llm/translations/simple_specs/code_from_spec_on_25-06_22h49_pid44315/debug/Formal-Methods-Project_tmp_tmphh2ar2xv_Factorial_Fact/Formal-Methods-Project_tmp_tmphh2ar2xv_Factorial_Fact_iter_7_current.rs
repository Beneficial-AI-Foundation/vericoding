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
        
        // Prove that the multiplication is well-defined
        assert(x > 0 && prev > 0);
        
        let result = x * prev;
        
        // Prove result equals fact_spec(x)
        assert(result == x * fact_spec(x - 1));
        assert(fact_spec(x) == x * fact_spec(x - 1)) by {
            // By definition of fact_spec when x > 0
        };
        assert(result == fact_spec(x));
        
        // Prove result >= 1
        assert(result >= 1) by {
            assert(x >= 1);
            assert(prev >= 1);
            // Since both x and prev are at least 1, their product is at least 1
        };
        
        result
    }
}

}