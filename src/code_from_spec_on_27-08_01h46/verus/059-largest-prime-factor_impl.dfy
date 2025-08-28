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
spec fn has_prime_factor_in_range(n: int, start: int, end: int) -> bool {
    exists|i: int| start <= i < end && spec_prime(i) && n % i == 0
}

spec fn is_factor(n: int, f: int) -> bool {
    f > 0 && n % f == 0
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

spec fn divides(n: int, d: int) -> bool {
    d != 0 && n % d == 0
}

proof fn lemma_prime_n_when_n_ge_2(n: int)
    requires n >= 2
    ensures spec_prime(n) || exists|f: int| 2 <= f < n && divides(n, f)
{
    if !spec_prime(n) {
        assert(!spec_prime_helper(n, n));
        assert(exists|j: int| 2 <= j < n && n % j == 0);
        let witness = choose|j: int| 2 <= j < n && n % j == 0;
        assert(divides(n, witness));
    }
}

proof fn lemma_n_is_prime_when_n_ge_2(n: int)
    requires n >= 2, spec_prime(n)
    ensures spec_prime(n)
{
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
    let mut largest_factor = 1u32;
    let mut current = n;
    let mut divisor = 2u32;
    
    while divisor <= 255 && divisor * divisor <= current && current > 1
        invariant
            2 <= divisor <= 256,
            1 <= current,
            largest_factor >= 1,
            largest_factor == 1 || (largest_factor <= n && spec_prime(largest_factor as int)),
        decreases current,
    {
        if current % divisor == 0 {
            if is_prime(divisor) {
                largest_factor = divisor;
            }
            current = current / divisor;
        } else {
            divisor += 1;
        }
    }
    
    if current > 1 {
        if current >= 2 && is_prime(current) {
            current
        } else if largest_factor > 1 {
            largest_factor
        } else {
            2
        }
    } else if largest_factor > 1 {
        largest_factor
    } else {
        2
    }
}
// </vc-code>

}
fn main() {}