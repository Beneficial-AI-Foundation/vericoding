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
{
    // impl-start
    let len_int = str.len() as int;
    if len_int < 2 {
        return false;
    } else {
        let mut k: int = 2;
        while k < len_int 
            invariant 
                2 <= k <= len_int,
                forall|i: int| 2 <= i < k ==> !is_divisible(len_int, i),
        {
            if is_divisible(len_int, k) {
                return false;
            }
            k = k + 1;
        }
        return true;
    }
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}