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
proof fn lemma_divisible_by_d(d: int, n: int)
    requires
        d > 0,
        n >= 0,
    ensures
        is_divisible(n, d) == (n % d == 0),
{
}

proof fn lemma_mod_properties(a: int, b: int)
    requires
        b > 0,
    ensures
        a % b >= 0,
        a % b < b,
{
}

spec fn divisors_up_to(n: int, limit: int) -> Set<int> {
    Set::new(|k: int| 2 <= k < limit && is_divisible(n, k))
}

proof fn lemma_nontrivial_divisor(n: int, k: int)
    requires
        n >= 2,
        2 <= k < n,
        is_divisible(n, k),
    ensures
        !is_prime(n),
{
}

proof fn lemma_prime_definition(n: int)
    ensures
        is_prime(n) == (
            if n < 2 {
                false
            } else {
                divisors_up_to(n, n).len() == 0
            }
        ),
{
    assert(divisors_up_to(n, n).len() == 0 == (forall|k: int| 2 <= k < n ==> !is_divisible(n, k)));
}

proof fn lemma_no_divisors_below_sqrt(n: int, sqrt: int)
    requires
        n >= 2,
        sqrt >= 1,
        sqrt * sqrt <= n,
        (sqrt + 1) * (sqrt + 1) > n,
    ensures
        forall|k: int| 2 <= k < n ==> is_divisible(n, k) == (2 <= k <= sqrt && is_divisible(n, k)),
{
    assert forall|k: int| 2 <= k < n implies is_divisible(n, k) == (2 <= k <= sqrt && is_divisible(n, k)) by {
        if is_divisible(n, k) {
            assert(k <= sqrt);
        }
    };
}

spec fn sqrt_floor(n: int) -> int
    recommends n >= 0
{
    if n < 2 {
        n
    } else {
        let mut i: int = 1;
        while i * i <= n
            invariant
                1 <= i,
                i * i <= n,
        {
            i = i + 1;
        }
        i - 1
    }
}

proof fn lemma_sqrt_properties(n: int)
    requires n >= 2,
    ensures
        let sqrt = sqrt_floor(n);
        sqrt >= 1,
        sqrt * sqrt <= n,
        (sqrt + 1) * (sqrt + 1) > n,
{
    let sqrt = sqrt_floor(n);
    assert(sqrt >= 1) by {
        assert(1 * 1 <= n);
    };
    assert(sqrt * sqrt <= n);
    assert((sqrt + 1) * (sqrt + 1) > n);
}
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
    let len_usize = str.len();
    let len: int = len_usize as int;
    if len < 2 {
        return false;
    }
    
    proof {
        lemma_sqrt_properties(len);
    }
    let sqrt: int = sqrt_floor(len);
    let mut i: int = 2;
    
    while i <= sqrt
        invariant
            2 <= i <= sqrt + 1,
            forall|k: int| 2 <= k < i ==> !is_divisible(len, k),
    {
        proof {
            lemma_mod_properties(len, i);
        }
        
        if len % i == 0 {
            proof {
                lemma_divisible_by_d(i, len);
                lemma_nontrivial_divisor(len, i);
            }
            return false;
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_no_divisors_below_sqrt(len, sqrt);
        lemma_prime_definition(len);
        assert(divisors_up_to(len, len).len() == 0);
    }
    
    true
}
// </vc-code>

} // verus!
fn main() {}