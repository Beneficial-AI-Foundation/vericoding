// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn mul_le(a: usize, b: usize, n: usize) -> (result: bool)
    ensures result == ((a as nat) * (b as nat) <= (n as nat))
{
    if a == 0 {
        true
    } else {
        // this is equivalent to a * b <= n but protects against overflow
        b <= n / a
    }
}

proof fn lemma_i_bound_by_n(i: usize, n: usize)
    requires
        (i as nat) * (i as nat) <= (n as nat),
    ensures
        i <= n || (n == 0 && i == 0) || (n == 1 && i <= 1) || (n == 2 && i <= 1) || (n == 3 && i <= 1),
{
    let ii = i as nat;
    let nn = n as nat;
    if i > n {
        if n >= 2 {
            let i_ge_n_plus_1 = i >= n + 1;
            let ii_ge_nn_plus_1 = ii >= nn + 1;
            assert(ii * ii >= (nn + 1) * (nn + 1));
            assert((nn + 1) * (nn + 1) == nn * nn + 2 * nn + 1);
            if nn > 0 {
                assert(nn * nn >= nn);
            }
            assert(nn * nn + 2 * nn + 1 > nn);
            assert(ii * ii > nn);
            assert(false);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    let mut r: usize = 0;
    while r < usize::MAX && mul_le(r + 1, r + 1, n)
        invariant
            (r as nat) * (r as nat) <= (n as nat),
            r <= n || (n == 0 && r == 0) || (n == 1 && r <= 1) || (n == 2 && r <= 1) || (n == 3 && r <= 1),
        decreases n - r
    {
        lemma_i_bound_by_n(r, n);
        r = r + 1;
    }
    r
}
// </vc-code>

}
fn main() {}