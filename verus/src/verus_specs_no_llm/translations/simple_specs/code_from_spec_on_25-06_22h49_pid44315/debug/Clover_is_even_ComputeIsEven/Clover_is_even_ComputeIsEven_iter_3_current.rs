use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeIsEven(x: int) -> (is_even: bool)
    ensures
        (x % 2 == 0) == is_even
    decreases x.abs()
{
    if x >= 0 {
        if x == 0 {
            true
        } else if x == 1 {
            false
        } else {
            assert(x >= 2);
            assert((x - 2).abs() < x.abs());
            let result = ComputeIsEven(x - 2);
            assert((x % 2 == 0) == ((x - 2) % 2 == 0)) by {
                // Mathematical property: x and x-2 have the same parity
                assert(x % 2 == (x - 2) % 2);
            };
            result
        }
    } else {
        assert(x < 0);
        assert((-x).abs() == x.abs());
        assert((-x) > 0);
        let result = ComputeIsEven(-x);
        assert((x % 2 == 0) == ((-x) % 2 == 0)) by {
            // Mathematical property: x and -x have the same parity
            assert(x % 2 == (-x) % 2);
        };
        result
    }
}

}