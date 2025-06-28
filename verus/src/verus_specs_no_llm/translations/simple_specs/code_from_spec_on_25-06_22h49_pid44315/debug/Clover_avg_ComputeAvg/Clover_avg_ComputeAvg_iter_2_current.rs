use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeAvg(a: int, b: int) -> (avg: int)
    ensures
        avg == (a+b)/2
{
    proof {
        assert(2 != 0);
    }
    (a + b) / 2
}

}