use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeAvg(a: int, b: int) -> (avg: int)
    ensures
        avg == (a + b) / 2
{
    let sum = a + b;
    let avg = sum / 2;
    assert(sum == a + b);
    assert(avg == sum / 2);
    assert(avg == (a + b) / 2);
    avg
}

}