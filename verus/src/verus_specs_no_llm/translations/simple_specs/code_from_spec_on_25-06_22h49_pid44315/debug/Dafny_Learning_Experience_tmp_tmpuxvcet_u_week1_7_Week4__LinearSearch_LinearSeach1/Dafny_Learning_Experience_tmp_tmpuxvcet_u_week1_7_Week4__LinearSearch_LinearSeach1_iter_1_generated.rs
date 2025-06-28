use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Empty main function - no specific requirements given
}

spec fn P(n: int) -> bool {
    n % 2 == 0
}

}