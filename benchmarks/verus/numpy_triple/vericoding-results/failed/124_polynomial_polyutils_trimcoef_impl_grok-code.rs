// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed return type from nat to int to fix compilation error, as nat cannot be used in executable code */
fn abs_f32(x: f32) -> f32 { if x >= 0.0 { x } else { -x } }
fn trim_len(c: Seq<f32>, tol: f32) -> (result: int)
    requires
        c.len() >=1,
    ensures
        result >=1,
        result <= c.len(),
        forall |j: int| 0 <= j < c.len() && j >= result ==> abs_f32(c@[j]) <= tol,
        exists |j: int| (0 <= j < c.len() && abs_f32(c@[j]) > tol) ==> (exists |i: int| 0 <= i < c.len() && abs_f32(c@[i]) > tol && i < result)
{
    let len = c.len();
    let mut i: isize = (len - 1) as isize;
    while i >= 0 && abs_f32(c@[i as usize]) <= tol
        invariant
            0 <= i+1,
            (i as usize) < c.len() || i == -1,
            forall |j: int| i < j && j < c.len() ==> abs_f32(c@[j]) <= tol,
        decreases (i + 1)
    {
        i -= 1;
    }
    if i >= 0 { ((i as usize) + 1) as int } else { 1 }
}
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): updated to handle new return type int for trim_len */
{
proof {
    assert(c.len() >= 1);
}
let seq_c = c@;
let result_len = trim_len(seq_c, tol);
proof {
    assert(result_len >= 1 && result_len <= c.len());
}
let mut result = Vec::with_capacity(result_len as usize);
for i in 0..(result_len as usize) {
    result.push(c[i]);
    proof {
        assert(i < c.len());
    }
}
result
}
// </vc-code>

}
fn main() {}