use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn triple_conditions(x: int) -> (r: int)
    ensures
        r == 3 * x
{
    let result = 3 * x;
    proof {
        assert(result == 3 * x);
    }
    result
}

}