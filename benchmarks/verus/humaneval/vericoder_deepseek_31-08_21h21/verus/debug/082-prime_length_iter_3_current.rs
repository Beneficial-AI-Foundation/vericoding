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
    let len = str.len() as int;
    if len < 2 {
        return false;
    }
    
    let sqrt = (len as f64).sqrt() as int;
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