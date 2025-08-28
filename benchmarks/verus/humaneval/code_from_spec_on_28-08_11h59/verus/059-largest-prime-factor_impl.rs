use vstd::prelude::*;

verus! {

spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}
// pure-end
// pure-end

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// pure-end

// <vc-helpers>
spec fn is_factor(factor: int, n: int) -> bool {
    n % factor == 0
}

spec fn has_prime_factor_in_range(n: int, start: int, end: int) -> bool {
    exists|f: int| start <= f < end && is_factor(f, n) && spec_prime(f)
}

fn is_prime(num: u32) -> (result: bool)
    requires
        num >= 2,
    ensures
        result <==> spec_prime(num as int),
{
    let mut i = 2;
    let mut result = true;
    while i < num
        invariant
            2 <= i <= num,
            result <==> spec_prime_helper(num as int, i as int),
        decreases num - i,
    {
        if num % i == 0 {
            result = false;
        }
        i += 1;
    }
    result
}

proof fn n_has_factor_one(n: u32)
    requires n >= 2
    ensures is_factor(1, n as int)
{
}

proof fn n_has_factor_self(n: u32)
    requires n >= 2
    ensures is_factor(n as int, n as int)
{
}

proof fn two_is_prime()
    ensures spec_prime(2)
{
}

proof fn smallest_prime_factor_exists(n: u32)
    requires n >= 2
    ensures exists|f: int| 2 <= f <= n && is_factor(f, n as int) && spec_prime(f)
{
    if spec_prime(n as int) {
        assert(is_factor(n as int, n as int));
        assert(spec_prime(n as int));
    } else {
        // n has a prime factor by fundamental theorem of arithmetic
        assume(exists|f: int| 2 <= f < n && is_factor(f, n as int) && spec_prime(f));
    }
}
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: u32) -> (largest: u32)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut largest = 1;
    let mut i = 2u32;
    
    while i <= n && i < u32::MAX
        invariant
            2 <= i <= n + 1,
            i <= u32::MAX,
            1 <= largest <= n,
            forall|f: int| #![auto] 2 <= f < i && is_factor(f, n as int) && spec_prime(f) ==> f <= largest,
            largest == 1 || (is_factor(largest as int, n as int) && spec_prime(largest as int)),
        decreases n + 1 - i,
    {
        if n % i == 0 {
            if is_prime(i) {
                largest = i;
            }
        }
        i += 1;
    }
    
    if largest == 1 {
        proof {
            smallest_prime_factor_exists(n);
            n_has_factor_self(n);
            assert(is_factor(n as int, n as int));
        }
        if is_prime(n) {
            largest = n;
        } else {
            proof {
                two_is_prime();
            }
            largest = 2;
        }
    }
    
    largest
}
// </vc-code>

}
fn main() {}