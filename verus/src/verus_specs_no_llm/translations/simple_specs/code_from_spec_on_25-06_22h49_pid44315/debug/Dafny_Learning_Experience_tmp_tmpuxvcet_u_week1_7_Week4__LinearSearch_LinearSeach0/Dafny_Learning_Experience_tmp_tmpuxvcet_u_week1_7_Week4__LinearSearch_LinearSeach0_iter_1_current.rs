use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Empty main function - no requirements specified
}

spec fn P(n: int) -> bool {
    n % 2 == 0
}

}