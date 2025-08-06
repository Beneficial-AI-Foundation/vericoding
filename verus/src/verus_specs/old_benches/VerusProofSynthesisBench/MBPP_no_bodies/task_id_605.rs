use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (result: bool) {
    (n % divisor) == 0
}
// pure-end

fn prime_num(n: u64) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
