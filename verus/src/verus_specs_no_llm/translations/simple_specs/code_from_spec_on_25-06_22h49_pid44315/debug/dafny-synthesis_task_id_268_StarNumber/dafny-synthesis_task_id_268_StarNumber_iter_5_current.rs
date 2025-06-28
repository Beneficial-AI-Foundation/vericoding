use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn StarNumber(n: int) -> int
    requires
        n >= 0
    ensures
        StarNumber(n) == 6 * n * (n - 1) + 1
{
    6 * n * (n - 1) + 1
}

}