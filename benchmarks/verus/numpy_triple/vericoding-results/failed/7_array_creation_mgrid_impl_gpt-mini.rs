// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute element as spec function */
spec fn compute_elem(start: i8, step: i8, idx: int) -> int {
    start as int + idx * step as int
}

/* helper modified by LLM (iteration 5): prove elements are < stop for indices < n */
proof fn compute_elem_lt_stop(start: i8, stop: i8, step: i8, n: usize)
    requires
        step > 0,
        start < stop,
        n == ((stop as int - start as int) / step as int) as usize,
    ensures
        forall|i: int| 0 <= i < n as int ==> compute_elem(start, step, i) < stop as int,
{
    proof {
        let a: int = stop as int - start as int;
        let k: int = step as int;
        let q: int = n as int;
        assert(q == a / k);
        assert(q * k <= a);
        assert(a < (q + 1) * k);
        forall |i: int| 0 <= i < q {
            assert(k > 0);
            assert(i * k < q * k);
            assert(q * k <= a);
            assert(i * k < a);
            assert(start as int + i * k < start as int + a);
            assert(start as int + a == stop as int);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn mgrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires
        step > 0,
        start < stop,
        n == ((stop as int - start as int) / step as int) as usize,
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] == start as int + i * step as int,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] < stop as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build vector with verified invariants and safe casts */
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v@.len() == i,
            forall|j: int| 0 <= j < v@.len() ==> #[trigger] v@[j] == start as int + j * step as int,
            forall|j: int| 0 <= j < v@.len() ==> #[trigger] v@[j] < stop as int,
        decreases n - i
    {
        proof {
            compute_elem_lt_stop(start, stop, step, n);
            let idx_spec: int = i as int;
            assert(start as int + idx_spec * step as int < stop as int);
            assert(start as int + idx_spec * step as int >= -128);
            assert(start as int + idx_spec * step as int <= 127);
        }
        let val_spec: int = start as int + (i as int) * (step as int);
        let val: i8 = #[verifier::truncate] (val_spec as i8);
        v.push(val);
        i = i + 1;
    }
    v
}
// </vc-code>


}
fn main() {}