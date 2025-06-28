use builtin::*;
use builtin_macros::*;

verus! {

spec fn even(n: int) -> bool {
    n % 2 == 0
}

fn main() {
}

fn is_even(n: int) -> (r: bool)
    requires
        n >= 0
    ensures
        r <==> even(n)
{
    n % 2 == 0
}

}