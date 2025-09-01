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
            forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j as int] == !is_divisible(n as int, j + 2),
    {
        let divisible = is_divisible(n as int, i as int);
        s.push(!divisible);
        if divisible {
            return false;
        }
        i = i + 1;
    }
    proof {
        lemma_forall_not_divisible_implies_prime(n as nat, s.to_seq());
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