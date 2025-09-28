// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed compilation errors and type inconsistencies in proof block. */
    let mut result = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == start as int + j * step as int,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] < stop as int,
        decreases n - i
    {
        let val_i32 = start as i32 + (i as i32) * (step as i32);

        proof {
            let s = start as int;
            let t = stop as int;
            let p = step as int;
            let val_int = s + (i as int) * p;
            
            assert(val_i32 as int == val_int);

            let q = (t - s) / p;
            assert(n as int == q);

            vstd::arithmetic::internals::div_internals::lemma_div_auto();

            assert((i as int) + 1 <= q);
            assert(((i as int) + 1) * p <= q * p);
            assert(q * p <= t - s);
            assert(val_int + p <= t);
            assert(val_int < t);
            
            assert(val_int >= s);
            
            assert(i8::MIN as int <= val_int && val_int <= i8::MAX as int);
        }

        let val = val_i32 as i8;
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}