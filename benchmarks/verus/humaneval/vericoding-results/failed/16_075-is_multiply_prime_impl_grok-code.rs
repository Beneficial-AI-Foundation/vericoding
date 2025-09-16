// <vc-preamble>
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Strengthened loop invariant in is_prime to ensure no divisors found */
fn is_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result <==> spec_prime((n as int))
{
    let mut i = 2u64;
    while i * i <= n
        invariant
            i >= 2,
            forall|j: int| 2 <= j < i ==> #[trigger] ((n as int) % j) != 0,
        decreases ((n as int) - (i as int))
    {
        if n % i == 0 {
            return false;
        }
        i += 1;
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(x: u32) -> (ans: bool)

    requires
        x > 1,

    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Corrected while loop syntax and updated counting logic to count distinct prime factors */
    let mut count: u64 = 0;
    let mut num: u64 = x as u64;
    let mut p: u64 = 2;
    while p * p <= num
    {
        if num % p == 0 && is_prime(p) {
            count += 1;
            let mut current_num = num;
            while current_num % p == 0
                invariant
                    current_num % p == 0,
                decreases current_num as int
            {
                current_num /= p;
            }
            num = current_num;
        }
        p += 1;
    }
    if num > 1 && is_prime(num) {
        count += 1;
    }
 (count == 3)
}
// </vc-code>

}
fn main() {}