// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (ret:bool) {
    (n % divisor) == 0
}

spec fn is_prime(n: int) -> (ret:bool) {
    if n < 2 {
        false
    } else {
        (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): equivalence between forall non-divisible and absence of an existential divisor */
proof fn lemma_forall_not_divisible_iff_no_exists(n: int)
    ensures
        (forall|k: int| 2 <= k < n ==> !is_divisible(n, k))
        == !(exists|k: int| 2 <= k < n && is_divisible(n, k)),
{
}

/* helper modified by LLM (iteration 3): step lemma for extending the existential range by one */
proof fn lemma_exists_step_div(n: int, i: int)
    requires
        2 <= i,
    ensures
        (exists|k: int| 2 <= k < i + 1 && is_divisible(n, k))
        == ((exists|k: int| 2 <= k < i && is_divisible(n, k)) || is_divisible(n, i)),
{
}

/* helper modified by LLM (iteration 3): relate executable usize modulo with spec-level int divisibility */
proof fn lemma_mod_compat_usize_int(n: usize, d: usize)
    requires
        d >= 1,
    ensures
        (n % d == 0) == is_divisible(n as int, d as int),
{
}
// </vc-helpers>

// <vc-spec>
fn prime_length(str: &[char]) -> (result: bool)

    ensures
        result == is_prime(str.len() as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement primality check with loop and ghost reasoning to maintain invariant */
    let n: usize = str.len();
    if n < 2 {
        return false;
    }
    let mut i: usize = 2;
    let mut found: bool = false;
    while i < n
        invariant
            (n as int) >= 2,
            2 <= (i as int) <= (n as int),
            found == (exists|k: int| 2 <= k < (i as int) && is_divisible(n as int, k)),
        decreases (n as int) - (i as int)
    {
        let oi = i;
        let prev_found = found;
        let divisible_now = n % oi == 0;
        found = prev_found || divisible_now;
        proof {
            lemma_mod_compat_usize_int(n, oi);
            assert(divisible_now == is_divisible(n as int, oi as int));
            assert(prev_found == (exists|k: int| 2 <= k < (oi as int) && is_divisible(n as int, k)));
            lemma_exists_step_div(n as int, oi as int);
            assert(found == ((exists|k: int| 2 <= k < (oi as int) && is_divisible(n as int, k)) || is_divisible(n as int, oi as int)));
            assert(found == (exists|k: int| 2 <= k < ((oi as int) + 1) && is_divisible(n as int, k)));
        }
        i = oi + 1;
    }
    proof {
        assert(i == n);
    }
    let result = !found;
    proof {
        lemma_forall_not_divisible_iff_no_exists(n as int);
        assert(result == !(exists|k: int| 2 <= k < (n as int) && is_divisible(n as int, k)));
        assert(result == is_prime(n as int));
    }
    result
}
// </vc-code>

}
fn main() {}