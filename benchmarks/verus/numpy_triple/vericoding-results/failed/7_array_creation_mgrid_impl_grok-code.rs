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
    /* code modified by LLM (iteration 5): fixed invariant syntax by combining equality and range conditions in one forall with &&, added proof asserts for range and less than stop */
    let mut v = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i >= 0,
            i <= n,
            i == v@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == start as int + j * step as int && i8::MIN as int <= v@[j] <= i8::MAX as int && v@[j] < stop as int,
        decreases n - i
    {
        let val_int = start as int + i as int * step as int;
        let val = val_int as i8;
        proof {
            assert(val as int == val_int);
            assert(i8::MIN as int <= val_int <= i8::MAX as int);
            assert(val_int <= start as int + (n as int - 1) * step as int);
            assert(start as int + (n as int - 1) * step as int < stop as int);
        }
        v.push(val);
        i += 1;
    }
    v
}
// </vc-code>


}
fn main() {}