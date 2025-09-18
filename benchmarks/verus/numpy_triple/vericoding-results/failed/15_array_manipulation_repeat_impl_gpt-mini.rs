// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove bounds of division */
proof fn div_bounds(i: int, repeats: usize, a_len: usize)
    requires repeats > 0,
             0 <= i && i < (a_len as int) * (repeats as int),
    ensures 0 <= i / (repeats as int) && i / (repeats as int) < (a_len as int)
{
    proof {
        let r = repeats as int;
        assert(r > 0);
        assert(0 <= i);
        assert(i < (a_len as int) * r);
        // From 0 <= i < a_len * r and r > 0, division yields 0 <= i / r < a_len
        assert(i / r >= 0);
        assert(i / r < a_len as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn repeat<T: Copy>(a: Vec<T>, repeats: usize) -> (result: Vec<T>)
    requires repeats > 0,
    ensures
        result.len() == a.len() * repeats,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let k = i / (repeats as int);
            0 <= k < a.len() && result[i] == a[k]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement repeat with corrected invariant syntax */
    let mut result: Vec<T> = Vec::new();
    let mut k: usize = 0;
    while k < a.len()
        invariant result.len() == k * repeats,
        invariant forall|i: int| 0 <= i && i < (result.len() as int) ==> 0 <= i / (repeats as int) && i / (repeats as int) < (k as int) && result@[i] == a@[(i / (repeats as int))],
        decreases a.len() - k
    {
        let elem: T = a[k];
        let mut c: usize = 0;
        while c < repeats
            invariant result.len() == k * repeats + c,
            invariant forall|i: int| 0 <= i && i < (result.len() as int) ==> ((0 <= i / (repeats as int) && i / (repeats as int) < (k as int) && result@[i] == a@[(i / (repeats as int))]) || (i / (repeats as int) == (k as int) && result@[i] == elem)),
            decreases repeats - c
        {
            result.push(elem);
            c += 1;
        }
        k += 1;
    }
    result
}
// </vc-code>

}
fn main() {}