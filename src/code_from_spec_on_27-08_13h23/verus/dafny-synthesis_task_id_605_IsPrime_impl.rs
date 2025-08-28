use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_divisible_by_smaller(n: int, k: int)
    requires
        2 <= k < n,
        n % k == 0,
    ensures
        !forall|j: int| 2 <= j < n ==> n % j != 0,
{
}

proof fn lemma_not_divisible_implies_prime(n: int)
    requires
        n >= 2,
        forall|k: int| 2 <= k < n ==> n % k != 0,
    ensures
        forall|j: int| 2 <= j < n ==> n % j != 0,
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
{
    let mut i = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> n % k != 0,
    {
        if n % i == 0 {
            proof {
                lemma_divisible_by_smaller(n, i);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        lemma_not_divisible_implies_prime(n);
    }
    true
}
// </vc-code>

fn main() {
}

}