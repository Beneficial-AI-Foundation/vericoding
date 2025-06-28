use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsOdd(n: int) -> bool {
    n % 2 == 1
}

}

The code is already correctly implemented:


This implementation satisfies the mathematical definition of an odd number and should verify correctly in Verus. The spec function can be used in specifications and proofs throughout the codebase to reason about odd numbers.