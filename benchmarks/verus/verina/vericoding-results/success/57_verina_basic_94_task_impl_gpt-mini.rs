// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): relate runtime index to spec sequence */
fn vec_index_spec(v: &Vec<i32>, idx: usize) -> (result: i32)
    requires
        idx < v.len(),
    ensures
        result == v@[idx as int],
{
    v[idx]
}

// </vc-helpers>

// <vc-spec>
fn iter_copy(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == result[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): copy elements from s into new vector with proper specs */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            (res@).len() == i as int,
            forall|j: int| 0 <= j < i as int ==> res@[j] == s@[j],
        decreases
            s.len() - i
    {
        let x: i32 = s[i];
        res.push(x);
        i = i + 1;
    }
    res
}

// </vc-code>

}
fn main() {}