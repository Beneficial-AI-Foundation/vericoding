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
proof fn lemma_div_mod(num: int, d: int)
    requires
        d > 0,
        num >= 0,
    ensures
        num % d < d,
        num % d >= 0,
{
}

proof fn lemma_div_leq(num: int, d: int)
    requires
        d > 0,
        num >= 0,
    ensures
        num / d <= num,
{
}

proof fn lemma_factor_transitivity(n: int, f: int, g: int)
    requires
        n % f == 0,
        f % g == 0,
        f > 0,
        g > 0,
    ensures
        n % g == 0,
{
    assert(0 == n % f == n - f * (n / f));
    assert(0 == f % g == f - g * (f / g));
    assert(n == f * (n / f) == g * (f / g) * (n / f));
    assert(n - g * ((f / g) * (n / f)) == 0);
    assert(n % g == 0);
}

proof fn lemma_mod_zero_implies_divisible(a: int, b: int)
    requires
        b != 0,
    ensures
        (a % b == 0) == (b * (a / b) == a),
{
    if a % b == 0 {
        assert(b * (a / b) == a - (a % b) == a);
    } else {
        assert(b * (a / b) == a - (a % b) != a);
    }
}

proof fn lemma_prime_helper_multiples(num: int, limit: int)
    requires
        num >= 2,
        limit >= 2,
        limit <= num,
    ensures
        spec_prime_helper(num, limit) == (forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0),
{
}

proof fn lemma_prime_helper_decreasing(num: int, limit1: int, limit2: int)
    requires
        num >= 2,
        2 <= limit2 <= limit1 <= num,
    ensures
        spec_prime_helper(num, limit1) ==> spec_prime_helper(num, limit2),
{
}

proof fn lemma_prime_implies_no_factors(num: int)
    requires
        spec_prime(num),
        num >= 2,
    ensures
        forall|d: int| 2 <= d < num ==> (#[trigger] (num % d)) != 0,
{
}

proof fn lemma_prime_factors_exist(n: int)
    requires
        n >= 2,
    ensures
        exists|d: int| 2 <= d <= n && #[trigger] (n % d) == 0 && spec_prime(d),
    decreases n
{
    if spec_prime(n) {
        assert(n % n == 0);
    } else {
        let mut d = 2;
        while d < n
            invariant
                2 <= d <= n,
            decreases n - d,
        {
            if n % d == 0 {
                lemma_prime_factors_exist(d);
                break;
            }
            d = d + 1;
        }
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
    let mut current = n;
    let mut largest = 1u32;
    let mut factor = 2u32;
    
    proof {
        lemma_prime_factors_exist(n as int);
    }
    
    assert(1 <= largest && largest <= n) by { 
        assert(1 <= 1 && 1 <= n); 
    }
    
    while factor <= current && factor * factor <= current
        invariant
            current >= 1,
            factor >= 2,
            largest >= 1,
            largest <= n,
            spec_prime(largest as int),
            current as int >= 1,
            factor as int >= 2,
        decreases
            current as int - factor as int,
    {
        if current % factor == 0 && factor > 0 {
            proof {
                lemma_div_mod(current as int, factor as int);
            }
            
            current = current / factor;
            largest = factor;
            
            proof {
                assert(spec_prime_helper(factor as int, factor as int));
                assert(spec_prime(factor as int));
            }
        } else {
            factor = factor + 1;
        }
    }
    
    if current > 1 {
        largest = current;
        
        proof {
            assert(spec_prime_helper(current as int, current as int));
            assert(spec_prime(current as int));
        }
    }
    
    largest
}
// </vc-code>

fn main() {}
}