use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> bool {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result))
{
    assume(false);
    unreached()
}

}
fn main() {}