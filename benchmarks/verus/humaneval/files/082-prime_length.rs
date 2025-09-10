use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (ret:bool) {
    (n % divisor) == 0
}

spec fn is_prime(n: int) -> (ret:bool) {
    if n < 2 {
        false
    } else {
        (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k))
    }
}

fn prime_length(str: &[char]) -> (result: bool)

    ensures
        result == is_prime(str.len() as int),
{
    assume(false);
    unreached();
}

}
fn main() {}