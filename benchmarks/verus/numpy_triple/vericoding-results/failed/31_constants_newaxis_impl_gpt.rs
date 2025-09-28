// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum NewAxis {
    Newaxis,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): create a 1-element Vec and specify its sequence */
fn singleton_row(x: i8) -> (r: Vec<i8>)
    ensures
        r@.len() == 1,
        r@[0] == x,
{
    let mut r: Vec<i8> = Vec::new();
    r.push(x);
    r
}
// </vc-helpers>

// <vc-spec>
fn expand_to_column(v: Vec<i8>, axis: NewAxis) -> (result: Vec<Vec<i8>>)
    ensures
        result@.len() == v@.len(),
        forall|i: int| 0 <= i < result@.len() ==> (
            result@[i].len() == 1 &&
            result@[i][0] == v@[i]
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix type mismatch in push-related assertions and reason with inner vector reflections */
    let n = v.len();
    let mut res: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            v@.len() == n as int,
            res@.len() == i as int,
            forall|j: int| 0 <= j < res@.len() ==> (((res@[j])@.len() == 1) && ((res@[j])@[0] == v@[j])),
        decreases n as int - i as int
    {
        let x = v[i];
        let mut row: Vec<i8> = Vec::new();
        proof { assert(row@.len() == 0); }
        row.push(x);
        proof {
            assert(row@.len() == 1);
            assert(row@[0] == x);
        }
        let ghost s_pre = res@;
        let ghost i_int = i as int;
        proof { assert(v@[i_int] == x); }
        res.push(row);
        proof {
            // After push, spec of res is s_pre.push(row)
            assert(s_pre.len() == i_int);
            assert(res@ == s_pre.push(row));
            // The newly appended element is exactly row
            assert(res@[i_int] == row);
            // And row encodes the singleton [v[i]]
            assert((res@[i_int])@.len() == 1);
            assert((res@[i_int])@[0] == v@[i_int]);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}