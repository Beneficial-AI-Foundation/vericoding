use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeAvg(a: int, b: int) -> (avg: int)
    ensures
        avg == builtin::spec_functions::math::div(a+b, 2)
{
    (a + b) / 2
}

}