// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): sum_step proof showing step from i to i+1 */
fn sum_step(i: nat) {
    proof {
        assert(
            i*(2*i+1)*(7 + 24*i*i*i - 12*i*i - 14*i) + 15*(2*i+1)*(2*i+1)*(2*i+1)*(2*i+1)
            == (i+1)*(2*(i+1)+1)*(7 + 24*(i+1)*(i+1)*(i+1) - 12*(i+1)*(i+1) - 14*(i+1))
        );
    }
}

/* helper modified by LLM (iteration 5): sum_base proof for base case */
fn sum_base() {
    proof {
        assert(0*(2*0+1)*(7 + 24*0*0*0 - 12*0*0 - 14*0) == 0);
    }
}

// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative summation using nat types */
    let mut i: nat = 0;
    let mut acc: nat = 0;
    while i < n
        invariant
            i <= n,
            acc * 15 == i * (2 * i + 1) * (7 + 24 * (i * i * i) - 12 * (i * i) - 14 * i),
        decreases n - i
    {
        let old_acc = acc;
        let odd = i + i + 1;
        let term = odd * odd * odd * odd;
        acc = old_acc + term;
        proof {
            assert(old_acc * 15 == i * (2 * i + 1) * (7 + 24 * (i * i * i) - 12 * (i * i) - 14 * i));
            sum_step(i);
            assert(old_acc * 15 + 15 * term == (i+1) * (2*(i+1)+1) * (7 + 24*(i+1)*(i+1)*(i+1) - 12*(i+1)*(i+1) - 14*(i+1)));
            assert(acc * 15 == (i+1) * (2*(i+1)+1) * (7 + 24*(i+1)*(i+1)*(i+1) - 12*(i+1)*(i+1) - 14*(i+1)));
        }
        i = i + 1;
    }
    acc
}

// </vc-code>

}
fn main() {}