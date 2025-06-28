use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDivisibleBy11(n: int) -> bool
{
    n % 11 == 0
}

}