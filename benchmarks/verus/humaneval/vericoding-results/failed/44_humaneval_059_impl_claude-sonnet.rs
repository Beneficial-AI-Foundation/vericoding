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
spec fn has_factor_in_range(n: int, start: int, end: int) -> bool {
    exists|k: int| start <= k <= end && #[trigger] (n % k) == 0
}

/* helper modified by LLM (iteration 5): added trigger annotation and proof bodies */
fn lemma_factor_exists(n: int)
    requires n > 1, !is_prime(n)
    ensures exists|k: int| 2 <= k < n && n % k == 0
{
    proof {
        assert(exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0) by {
            let witness = 2;
            if n % 2 == 0 {
                assert(2 <= 2 < n && n % 2 == 0);
            } else {
                assert(exists|k: int| 3 <= k < n && n % k == 0);
            }
        }
    }
}

fn lemma_largest_factor_is_prime(n: int, largest: int)
    requires 
        n > 1,
        largest > 1,
        n % largest == 0,
        forall|k: int| k > largest && n % k == 0 ==> !is_prime(k)
    ensures is_prime(largest) || exists|p: int| p > largest && n % p == 0 && is_prime(p)
{
    proof {
        if !is_prime(largest) {
            assert(exists|f: int| 2 <= f < largest && largest % f == 0);
        }
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
{
    /* code modified by LLM (iteration 5): fixed syntax error with comma in invariant */
    let mut largest_factor = 2i8;
    let mut i = 2i8;
    
    while i <= n / 2
        invariant
            2 <= i <= n / 2 + 1,
            largest_factor >= 2,
            (n as int) % (largest_factor as int) == 0,
            is_prime(largest_factor as int),
            forall|k: int| largest_factor as int < k <= (i - 1) as int && (n as int) % k == 0 ==> !is_prime(k)
        decreases n / 2 - i + 1
    {
        if n % i == 0 {
            let mut is_prime_i = true;
            let mut j = 2i8;
            
            while j * j <= i
                invariant
                    2 <= j,
                    is_prime_i ==> forall|k: int| 2 <= k < j as int ==> (i as int) % k != 0
                decreases i - j * j + 1
            {
                if i % j == 0 {
                    is_prime_i = false;
                    break;
                }
                j = j + 1;
            }
            
            if is_prime_i {
                largest_factor = i;
            }
        }
        i = i + 1;
    }
    
    largest_factor
}
// </vc-code>


}

fn main() {}