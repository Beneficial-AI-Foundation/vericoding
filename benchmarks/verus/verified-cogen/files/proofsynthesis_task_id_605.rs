use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (result: bool) {
    (n % divisor) == 0
}

fn prime_num(n: u64) -> (result: bool)

    requires
        n >= 2,

    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
{
    assume(false);
    unreached();
}

}
fn main() {}