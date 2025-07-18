use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}
// pure-end

fn is_non_prime(n: u64) -> (result: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): moved requires/ensures clauses to correct position before function body */
    let mut k = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k ==> !is_divisible(n as int, j),
    {
        if n % k == 0 {
            return true;
        }
        k += 1;
    }
    return false;
}

} // verus!

fn main() {}