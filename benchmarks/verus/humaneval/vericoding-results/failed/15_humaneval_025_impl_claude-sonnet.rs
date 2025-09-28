// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n >= 2 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn product(factors: Seq<int>) -> int
    decreases factors.len()
{
    if factors.len() == 0 {
        1
    } else {
        factors[0] * product(factors.subrange(1, factors.len() as int))
    }
}

spec fn is_non_decreasing(factors: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < factors.len() ==> #[trigger] factors[i] <= #[trigger] factors[j]
}

// </vc-preamble>

// <vc-helpers>
proof fn product_non_empty(factors: Seq<int>)
    requires factors.len() > 0
    ensures product(factors) == factors[0] * product(factors.subrange(1, factors.len() as int))
{
}

proof fn product_append(factors1: Seq<int>, factors2: Seq<int>)
    ensures product(factors1 + factors2) == product(factors1) * product(factors2)
    decreases factors1.len()
{
    if factors1.len() == 0 {
        assert(factors1 + factors2 == factors2);
        assert(product(factors1) == 1);
    } else {
        let tail1 = factors1.subrange(1, factors1.len() as int);
        assert(factors1 + factors2 == seq![factors1[0]] + (tail1 + factors2));
        product_append(tail1, factors2);
        assert(product(tail1 + factors2) == product(tail1) * product(factors2));
        assert(product(factors1 + factors2) == factors1[0] * product(tail1 + factors2));
        assert(product(factors1 + factors2) == factors1[0] * product(tail1) * product(factors2));
        assert(product(factors1) == factors1[0] * product(tail1));
    }
}

proof fn product_positive(factors: Seq<int>)
    requires forall|i: int| 0 <= i < factors.len() ==> factors[i] >= 2
    ensures product(factors) >= 1
    decreases factors.len()
{
    if factors.len() == 0 {
        assert(product(factors) == 1);
    } else {
        let tail = factors.subrange(1, factors.len() as int);
        assert(forall|i: int| 0 <= i < tail.len() ==> tail[i] >= 2);
        product_positive(tail);
        assert(product(tail) >= 1);
        assert(factors[0] >= 2);
        assert(product(factors) == factors[0] * product(tail));
        assert(product(factors) >= 2 * 1);
    }
}

fn is_divisible(n: i8, d: i8) -> (result: bool)
    requires d > 0
    ensures result == (n % d == 0)
{
    let remainder = n % d;
    remainder == 0
}

/* helper modified by LLM (iteration 5): fixed type constraints and overflow */
fn find_smallest_factor(n: i8) -> (factor: i8)
    requires n >= 2, n <= 100
    ensures 
        2 <= factor <= n,
        n % factor == 0,
        forall|k: int| 2 <= k < factor ==> #[trigger] ((n as int) % k) != 0
{
    let mut i: i8 = 2;
    while i <= n
        invariant
            2 <= i <= n + 1,
            i <= 101,
            forall|k: int| 2 <= k < i ==> #[trigger] ((n as int) % k) != 0
        decreases (n - i) as nat
    {
        if n % i == 0 {
            return i;
        }
        i = i + 1;
    }
    n
}
// </vc-helpers>

// <vc-spec>
fn factorize(n: i8) -> (factors: Vec<i8>)
    requires n >= 0
    ensures 
        n <= 1 ==> factors.len() == 0,
        n > 1 ==> product(factors@.map(|i: int, x: i8| x as int)) == n as int,
        forall|i: int| 0 <= i < factors.len() ==> is_prime(#[trigger] factors@[i] as int),
        is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
        forall|i: int| 0 <= i < factors.len() ==> #[trigger] factors@[i] >= 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trigger annotation */
    if n <= 1 {
        return Vec::new();
    }
    
    let mut factors = Vec::new();
    let mut remaining = n;
    
    while remaining > 1
        invariant
            remaining >= 1,
            remaining <= n,
            n <= 100,
            product(factors@.map(|i: int, x: i8| x as int)) * (remaining as int) == n as int,
            forall|i: int| 0 <= i < factors.len() ==> is_prime(#[trigger] factors@[i] as int),
            is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
            forall|i: int| 0 <= i < factors.len() ==> #[trigger] factors@[i] >= 2
        decreases remaining
    {
        let factor = find_smallest_factor(remaining);
        
        proof {
            // Prove factor is prime
            assert(forall|k: int| 2 <= k < factor ==> #[trigger] ((remaining as int) % k) != 0);
            assert(factor >= 2);
            assert(remaining % factor == 0);
            assert(factor <= remaining);
            
            // Since factor is the smallest divisor >= 2, it must be prime
            assert(forall|k: int| 2 <= k < factor ==> #[trigger] ((factor as int) % k) != 0) by {
                if exists|k: int| 2 <= k < factor && (factor as int) % k == 0 {
                    let k_witness = choose|k: int| 2 <= k < factor && (factor as int) % k == 0;
                    assert((remaining as int) % k_witness == 0);
                    assert(false); // contradiction with factor being smallest
                }
            };
            assert(is_prime(factor as int));
            
            // Prove ordering
            if factors.len() > 0 {
                let last_factor = factors@[factors.len() - 1];
                // remaining was divided by last_factor, so factor >= last_factor
                assert(last_factor <= factor);
            }
        }
        
        factors.push(factor);
        remaining = remaining / factor;
    }
    
    proof {
        assert(remaining == 1);
        product_positive(factors@.map(|i: int, x: i8| x as int));
    }
    
    factors
}
// </vc-code>


}

fn main() {}