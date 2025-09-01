use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (ret:bool) {
    (n % divisor) == 0
}
// pure-end
// pure-end

spec fn is_prime(n: int) -> (ret:bool) {
    if n < 2 {
        false
    } else {
        (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k))
    }
}
// pure-end

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn prime_length(str: &[char]) -> (result: bool)
    // post-conditions-start
    ensures
        result == is_prime(str.len() as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{proof! use vstd::arithmetic::power2::lem_power2_gt_1;}
let n: int = str.len() as int;
if n < 2 {
    return false;
}
let mut k: int = 2;
while k < n 
    invariant
		2 <= k <= n,
		forall|m: int| 2 <= m < k ==> !(#[trigger] is_divisible(n, m)),
	{

    if #[trigger] is_divisible(n, k) {
        return false;
    }
    k = k + 1;
}
return true;
{proof! use vstd::arithmetic::div_mod::{lem_mod_of_mul, lem_mod_equal};}
// </vc-code>

} // verus!
fn main() {}