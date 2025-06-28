use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsNegative(n: int) -> bool {
    n < 0
}

}