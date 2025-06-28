use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

exec fn MedianLength(a: i32, b: i32) -> (median: i32)
    requires
        a > 0 && b > 0,
        a + b >= 0,  // prevent overflow
    ensures
        median == (a + b) / 2
{
    let median = (a + b) / 2;
    median
}

}