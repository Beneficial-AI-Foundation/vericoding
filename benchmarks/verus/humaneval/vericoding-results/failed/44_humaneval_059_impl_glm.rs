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
/* helper modified by LLM (iteration 4): remove non-ghost int variables, use i8 in computations */
fn is_prime_exec(n: i8) -> (b: bool)
    requires n as int >= 0
    ensures b == is_prime(n as int)
{
    if n < 2 {
        return false;
    }
    let mut i = 2;
    while i * i <= n
        invariant
            2 <= i,
            forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k) != 0
        decreases (n as int - i as int)
    {
        if n % i == 0 {
            return false;
        }
        i += 1;
    }
    true
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
/* code modified by LLM (iteration 4): remove non-ghost int variables, use i8 in computations */
{
    let mut candidate = n - 1;
    while candidate >= 2
        invariant
            candidate as int >= 1,
            forall|f: int| (candidate as int) < f < n as int && #[trigger] (n as int % f) == 0 ==> !is_prime(f)
        decreases candidate
    {
        if n % candidate == 0 {
            if is_prime_exec(candidate) {
                return candidate;
            }
        }
        candidate -= 1;
    }
    assert(false);
    2
}
// </vc-code>


}

fn main() {}