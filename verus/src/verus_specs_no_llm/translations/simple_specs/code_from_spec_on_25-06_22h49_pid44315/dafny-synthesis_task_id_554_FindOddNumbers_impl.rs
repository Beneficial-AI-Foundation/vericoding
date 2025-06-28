use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsOdd(n: int) -> bool {
    n % 2 == 1
}

}