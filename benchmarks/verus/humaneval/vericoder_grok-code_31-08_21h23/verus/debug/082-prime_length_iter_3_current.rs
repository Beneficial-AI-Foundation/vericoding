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
let n_usize = str.len();
ghost n_ghost: int = n_usize as int;
if n_ghost < 2 {
    return false;
}
let mut k: usize = 2;
ghost var k_ghost: int = 2;
while k < n_usize
    invariant
        n_ghost == n_usize as int,
        k_ghost == k as int,
        2 <= k_ghost <= n_ghost,
        forall|m: int| 2 <= m < k_ghost ==> !is_divisible(n_ghost, m),
{
    proof {
        assert(k != 0);
    }
    if n_usize % k == 0 {
        proof {
            assert(is_divisible(n_ghost, k_ghost));
        }
        return false;
    }
    proof {
        assert(!#[trigger] is_divisible(n_ghost, k_ghost));
    }
    k = k + 1;
    k_ghost = k_ghost + 1;
}
return true;
}
// </vc-code>

} // verus!
fn main() {}