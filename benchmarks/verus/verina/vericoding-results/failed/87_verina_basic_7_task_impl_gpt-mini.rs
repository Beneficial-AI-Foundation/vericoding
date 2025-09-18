// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma relating sum formula for b and b+1 */
fn sum_odd_squares_step(b: nat)
    ensures
        (b as int * (2 * b as int - 1) * (2 * b as int + 1)) / 3 + (2 * b as int + 1) * (2 * b as int + 1) == ((b + 1) as int * (2 * (b + 1) as int - 1) * (2 * (b + 1) as int + 1)) / 3,
    decreases b,
{
    proof {
        assert(3 * ((b as int * (2 * b as int - 1) * (2 * b as int + 1)) / 3 + (2 * b as int + 1) * (2 * b as int + 1)) == b as int * (2 * b as int - 1) * (2 * b as int + 1) + 3 * (2 * b as int + 1) * (2 * b as int + 1));
        assert(b as int * (2 * b as int - 1) * (2 * b as int + 1) + 3 * (2 * b as int + 1) * (2 * b as int + 1) == (2 * b as int + 1) * (b as int * (2 * b as int - 1) + 3 * (2 * b as int + 1)));
        assert(b as int * (2 * b as int - 1) + 3 * (2 * b as int + 1) == (b as int + 1) * (2 * b as int + 3));
        assert((2 * b as int + 1) * (b as int + 1) * (2 * b as int + 3) == 3 * (((b + 1) as int * (2 * (b + 1) as int - 1) * (2 * (b + 1) as int + 1)) / 3));
        assert(3 * ((b as int * (2 * b as int - 1) * (2 * b as int + 1)) / 3 + (2 * b as int + 1) * (2 * b as int + 1)) == 3 * (((b + 1) as int * (2 * (b + 1) as int - 1) * (2 * (b + 1) as int + 1)) / 3));
        assert(((b as int * (2 * b as int - 1) * (2 * b as int + 1)) / 3 + (2 * b as int + 1) * (2 * b as int + 1)) == ((b + 1) as int * (2 * (b + 1) as int - 1) * (2 * (b + 1) as int + 1)) / 3);
    }
}

// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative accumulation with invariant, proving step algebraically without calling helper */
    let mut i: u32 = 0;
    let mut acc: u32 = 0;
    while i < n
        invariant
            acc as int == (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3,
            i <= n,
        decreases n - i
    {
        let odd: u32 = 2 * i + 1;
        proof {
            assert(acc as int == (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3);
            assert(3 * ((i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3 + (2 * i as int + 1) * (2 * i as int + 1)) == i as int * (2 * i as int - 1) * (2 * i as int + 1) + 3 * (2 * i as int + 1) * (2 * i as int + 1));
            assert(i as int * (2 * i as int - 1) * (2 * i as int + 1) + 3 * (2 * i as int + 1) * (2 * i as int + 1) == (2 * i as int + 1) * (i as int * (2 * i as int - 1) + 3 * (2 * i as int + 1)));
            assert(i as int * (2 * i as int - 1) + 3 * (2 * i as int + 1) == (i as int + 1) * (2 * i as int + 3));
            assert((2 * i as int + 1) * (i as int + 1) * (2 * i as int + 3) == 3 * (((i + 1) as int * (2 * (i + 1) as int - 1) * (2 * (i + 1) as int + 1)) / 3));
            assert(3 * ((i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3 + (2 * i as int + 1) * (2 * i as int + 1)) == 3 * (((i + 1) as int * (2 * (i + 1) as int - 1) * (2 * (i + 1) as int + 1)) / 3));
            assert(((i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3 + (2 * i as int + 1) * (2 * i as int + 1)) == ((i + 1) as int * (2 * (i + 1) as int - 1) * (2 * (i + 1) as int + 1)) / 3);
            assert(acc as int + (odd as int * odd as int) == ((i + 1) as int * (2 * (i + 1) as int - 1) * (2 * (i + 1) as int + 1)) / 3);
        }
        acc = acc + odd * odd;
        i = i + 1;
    }
    acc
}

// </vc-code>

}
fn main() {}