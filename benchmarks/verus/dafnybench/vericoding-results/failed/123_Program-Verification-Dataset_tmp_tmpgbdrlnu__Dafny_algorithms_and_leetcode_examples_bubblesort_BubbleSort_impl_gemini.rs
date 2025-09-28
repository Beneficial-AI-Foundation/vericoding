// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn n_choose_2(n: int) -> int
{
    n * (n - 1) / 2
}

spec fn sum_range(lo: int, hi: int) -> int
    decreases hi - lo
{
    if lo >= hi { 0 }
    else { sum_range(lo, hi - 1) + hi - 1 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): reviewed and confirmed correctness */
proof fn lemma_sum_range_unroll_lo(lo: int, hi: int)
    requires
        lo < hi,
    ensures
        sum_range(lo, hi) == lo + sum_range(lo + 1, hi),
    decreases hi - lo
{
    if lo + 1 < hi {
        lemma_sum_range_unroll_lo(lo, hi - 1);
    }
}

/* helper modified by LLM (iteration 3): reviewed and confirmed correctness */
proof fn lemma_sum_range_is_n_choose_2(n: int)
    requires
        n >= 0,
    ensures
        sum_range(0, n) == n_choose_2(n),
    decreases n
{
    if n > 0 {
        lemma_sum_range_is_n_choose_2(n - 1);
        assert(n_choose_2(n) == n_choose_2(n - 1) + n - 1) by(nonlinear_arith)
            requires
                n > 0,
        ;
        assert(sum_range(0, n) == n_choose_2(n));
    }
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>) -> (n: usize) 
    ensures n <= n_choose_2(a.len() as int) as usize
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation error by manually implementing swap */
    let mut n: usize = 0;
    let len = a.len();
    if len <= 1 {
        return 0;
    }

    let mut i: usize = 0;
    while i < len - 1
        invariant
            len > 1,
            0 <= i <= len - 1,
            a.len() == len,
            n <= sum_range(len as int - i as int, len as int),
        decreases len - 1 - i
    {
        let limit = len - 1 - i;
        let mut j: usize = 0;
        while j < limit
            invariant
                len > 1,
                0 <= i < len - 1,
                limit == len - 1 - i,
                0 <= j <= limit,
                a.len() == len,
                n <= sum_range(len as int - i as int, len as int) + j as int,
            decreases limit - j
        {
            if a[j] > a[j + 1] {
                let tmp = a[j];
                a.set(j, a[j + 1]);
                a.set(j + 1, tmp);
                n = n + 1;
            }
            j = j + 1;
        }

        proof {
            lemma_sum_range_unroll_lo(len as int - i as int - 1, len as int);
        }
        i = i + 1;
    }

    proof {
        if len > 0 {
            // prove sum_range(1, len) == sum_range(0, len)
            lemma_sum_range_unroll_lo(0, len as int);
        }
        // prove sum_range(0, len) == n_choose_2(len)
        lemma_sum_range_is_n_choose_2(len as int);
    }
    
    n
}
// </vc-code>

}
fn main() {}