// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n > 1 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn power_of_2_factor(n: int, current: int) -> int
    recommends n > 0 && current > 0
    decreases current
    when current > 0
{
    if current % 2 != 0 { 1 }
    else { 2 * power_of_2_factor(n, current / 2) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added #[trigger] to modulo operation in invariant for proper verification */
exec fn is_prime_exec(n: int) -> bool
    requires
        n >= 0,
    ensures
        n > 1 ==> is_prime_exec(n) == is_prime(n),
{
    if n <= 1 {
        false
    } else {
        let ghost mut i: int = 2;
        while i * i <= n
            invariant
                n > 1,
                forall|k: int| 2 <= k < i ==> #[trigger] (n % k) != 0,
            decreases n - i
        {
            if n % i == 0 {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: i8) -> (result: i8)
    requires 
        n as int > 1,
        !is_prime(n as int),
    ensures 
        result as int > 1,
        (n as int) % (result as int) == 0,
        forall|k: int| k > result as int && (n as int) % k == 0 ==> !is_prime(k),
        is_prime(result as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed 'ghost' from invariant conditions */
{
    let ghost n_int: int = n as int;
    let ghost mut d: int = n_int / 2;
    let mut result: i8 = 0;
    let mut found = false;
    while d >= 2 && !found
        invariant
            d <= n_int / 2,
            d >= 1,
            !found,
        decreases d
    {
        if n_int % d == 0 && is_prime_exec(d) {
            result = d as i8;
            found = true;
        }
        d = d - 1;
    }
    result
}
// </vc-code>


}

fn main() {}