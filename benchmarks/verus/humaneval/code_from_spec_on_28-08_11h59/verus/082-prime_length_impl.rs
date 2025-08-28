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
proof fn lemma_small_numbers_not_prime()
    ensures !is_prime(0),
    ensures !is_prime(1),
{
}

proof fn lemma_two_is_prime()
    ensures is_prime(2),
{
    assert forall|k: int| 2 <= k < 2 ==> !is_divisible(2, k) by {
        // Empty range, so vacuously true
    }
}

proof fn lemma_divisible_by_self(n: int)
    requires n > 0,
    ensures is_divisible(n, n),
{
    assert((n % n) == 0);
}

proof fn lemma_not_prime_composite(n: int, k: int)
    requires n >= 2,
    requires 2 <= k < n,
    requires is_divisible(n, k),
    ensures !is_prime(n),
{
    assert(!is_prime(n)) by {
        assert(!(forall|j: int| 2 <= j < n ==> !is_divisible(n, j))) by {
            assert(2 <= k < n && is_divisible(n, k));
        }
    }
}

fn check_divisible(n: usize, k: usize) -> (result: bool)
    requires k > 0,
    ensures result == is_divisible(n as int, k as int),
{
    (n % k) == 0
}

fn is_prime_impl(n: usize) -> (result: bool)
    ensures result == is_prime(n as int),
{
    if n < 2 {
        proof {
            if n == 0 {
                lemma_small_numbers_not_prime();
            } else if n == 1 {
                lemma_small_numbers_not_prime();
            }
        }
        false
    } else if n == 2 {
        proof {
            lemma_two_is_prime();
        }
        true
    } else {
        let mut k = 2;
        while k < n
            invariant 
                2 <= n,
                2 <= k <= n,
                forall|j: int| 2 <= j < k ==> !is_divisible(n as int, j),
        {
            if check_divisible(n, k) {
                proof {
                    lemma_not_prime_composite(n as int, k as int);
                }
                return false;
            }
            k = k + 1;
        }
        true
    }
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
    is_prime_impl(str.len())
}
// </vc-code>

} // verus!
fn main() {}