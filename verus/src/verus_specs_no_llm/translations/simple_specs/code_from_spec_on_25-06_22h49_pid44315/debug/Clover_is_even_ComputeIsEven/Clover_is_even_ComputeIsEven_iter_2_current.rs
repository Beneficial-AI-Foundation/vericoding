use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeIsEven(x: int) -> (is_even: bool)
    ensures
        (x % 2 == 0) == is_even
{
    // Since we can't directly compute x % 2 for int in executable code,
    // we need to use a different approach
    // We'll use the mathematical property that an integer is even
    // if it's divisible by 2
    if x >= 0 {
        if x == 0 {
            true
        } else if x == 1 {
            false
        } else {
            ComputeIsEven(x - 2)
        }
    } else {
        // For negative numbers, use the property that x is even iff -x is even
        ComputeIsEven(-x)
    }
}

}