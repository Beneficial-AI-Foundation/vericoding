// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec function for computing the shift amount used in fftshift */
pub open spec fn shift_amount(n: int) -> int {
    n - n / 2
}
// </vc-helpers>

// <vc-spec>
fn fftshift(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i as int] == x[((i + (x.len() as int) - (x.len() as int) / 2) % (x.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove exec ints; compute indices with usize and prove equivalence to spec formula */
    let n = x.len();
    if n == 0 {
        return Vec::new();
    }
    let mut res: Vec<f32> = Vec::new();
    res.reserve(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            forall|j: int|
                0 <= j < i as int ==> res@[j] == x@[((j + (n as int) - ((n as int) / 2)) % (n as int))],
        decreases n - i
    {
        let s: usize = n / 2;
        let idx: usize = if i >= s {
            i - s
        } else {
            let diff: usize = s - i;
            n - diff
        };
        proof {
            let n_int: int = n as int;
            let i_int: int = i as int;
            let s_int: int = (n as int) / 2;
            assert(0 < n_int);
            if i >= s {
                assert(i_int >= s_int);
                assert(0 <= i_int - s_int);
                assert(i - s < n);
                assert(i_int - s_int < n_int);
                assert((((i_int + n_int) - s_int) % n_int) == (i_int - s_int));
                assert(idx as int == i_int - s_int);
            } else {
                assert(i_int < s_int);
                let diff: usize = s - i;
                let diff_int: int = diff as int;
                assert(diff_int == s_int - i_int);
                assert(0 < diff_int);
                assert(idx as int == (n_int - diff_int));
                assert(0 <= (idx as int) && (idx as int) < n_int);
                assert((((i_int + n_int) - s_int) % n_int) == (n_int - (s_int - i_int)));
            }
        }
        assert(idx < n);
        let v = x[idx];
        let old_i = i;
        res.push(v);
        proof {
            assert(res@[old_i as int] == v);
        }
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}