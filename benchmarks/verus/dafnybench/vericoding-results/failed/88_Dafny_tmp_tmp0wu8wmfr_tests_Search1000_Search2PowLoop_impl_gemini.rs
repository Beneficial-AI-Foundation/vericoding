// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_2_pow(n: int) -> bool
    decreases n
{
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_2_pow(n / 2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
proof fn lemma_is_2_pow_half(n: int)
    requires
        n > 1,
        is_2_pow(n),
    ensures
        is_2_pow(n / 2),
        n % 2 == 0,
{
}
// </vc-helpers>

// <vc-spec>
fn search_2_pow_loop(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    requires
        i <= i + n <= a.len(),
        forall|p: int, q: int| i <= p < q < (i + n) && 0 <= p < a.len() && 0 <= q < a.len() ==> 
            a@[p] <= a@[q],
        is_2_pow((n + 1) as int),
    ensures
        i <= k <= i + n,
        forall|r: int| i <= r < k && 0 <= r < a.len() ==> a@[r] < x,
        forall|r: int| k <= r < (i + n) && 0 <= r < a.len() ==> a@[r] >= x,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed invariants to use mathematical integers to prevent overflow errors. */
    let mut k = i;
    let mut len = n;
    while len > 0
        invariant
            i as int <= k as int,
            (k as int) + (len as int) <= (i as int) + (n as int),
            is_2_pow((len + 1) as int),
            forall|r: int| i <= r < k && 0 <= r < a.len() ==> a@[r] < x,
            forall|r: int| (k as int) + (len as int) <= r < (i as int) + (n as int) && 0 <= r < a.len() ==> a@[r] >= x,
        decreases len
    {
        proof {
            lemma_is_2_pow_half((len + 1) as int);
        }

        let half = len / 2;
        let m = k + half;

        if a[m] < x {
            k = m + 1;
        }
        
        len = half;
    }
    k
}
// </vc-code>

}
fn main() {}