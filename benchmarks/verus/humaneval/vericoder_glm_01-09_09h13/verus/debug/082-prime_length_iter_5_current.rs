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
proof fn lemma_forall_not_divisible_implies_prime(n: nat, s: Seq<bool>)
    requires
        n >= 2,
        s.len() == n - 1,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == !is_divisible(n as int, i + 2),
    ensures
        is_prime(n as int),
{
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
}

proof fn lemma_exec_divisible_eq_spec(n: nat, i: nat)
    requires
        2 <= i < n,
    ensures
        (n % i == 0) == is_divisible(n as int, i as int),
{
    assert((n as int) % (i as int) == (n % i) as int);
    assert(is_divisible(n as int, i as int) == ((n as int) % (i as int) == 0));
    assert(((n as int) % (i as int) == 0) == ((n % i) as int == 0));
    assert(((n % i) as int == 0) == (n % i == 0));
}

fn check_prime_seq(n: usize) -> (result: bool)
    ensures
        result ==> is_prime(n as int),
{
    if n < 2 {
        return false;
    }
    let mut s: Vec<bool> = Vec::new();
    let mut i: usize = 2;
    while i < n
        invariant
            n >= 2,
            2 <= i <= n,
            s.len() == i - 2,
            forall|j: int| 0 <= j < s.len() ==> #[trigger] s@[j] == !is_divisible(n as int, j + 2),
        decreases n - i
    {
        proof {
            assert(i as int + 2 == i + 2);
        }
        let divisible = (n % i == 0);
        proof {
            lemma_exec_divisible_eq_spec(n as nat, i as nat);
            assert(divisible == is_divisible(n as int, i as int));
        }
        s.push(!divisible);
        if divisible {
            return false;
        }
        i = i + 1;
    }
    proof {
        lemma_forall_not_divisible_implies_prime(n as nat, s@);
    }
    true
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
    check_prime_seq(str.len())
}
// </vc-code>

} // verus!
fn main() {}