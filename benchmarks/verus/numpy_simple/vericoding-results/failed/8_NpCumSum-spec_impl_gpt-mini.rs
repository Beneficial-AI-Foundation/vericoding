// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): convert usize to int */
spec fn usize_to_int(u: usize) -> int
    ensures
        result == u as int,
{
    u as int
}

/* helper modified by LLM (iteration 4): usize less-than implies int less-than */
spec fn usize_lt_to_int(i: usize, n: usize)
    requires
        i < n,
    ensures
        (i as int) < (n as int),
{
    assert((i as int) < (n as int));
    ()
}
// </vc-helpers>

// <vc-spec>
fn cum_sum(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> result[i as int] as int == result[(i - 1) as int] as int + a[i as int] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implement cumulative sum with proofs */
    let n: usize = a.len();
    proof {
        assert(n > 0);
    }
    let mut res: Vec<i8> = Vec::new();
    let mut acc: i32 = a[0] as i32;
    res.push(a[0]);
    let mut i: usize = 1;
    while i < n
        invariant
            res.len() == i,
            res.len() <= n,
            forall|j: usize| 1 <= j && j < i ==> res[j] as i32 == res[j - 1] as i32 + a[j] as i32,
        decreases n - i
    {
        acc = acc + a[i] as i32;
        res.push(acc as i8);
        i = i + 1;
    }
    proof {
        assert(res.len() == i);
        assert(!(i < n));
        assert(i >= n);
        assert(i <= n);
        assert(i == n);
    }
    res
}
// </vc-code>


}
fn main() {}