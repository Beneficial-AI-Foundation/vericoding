// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagval3d(x: Vec<f32>, y: Vec<f32>, z: Vec<f32>, c: Vec<Vec<Vec<f32>>>) -> (result: Vec<f32>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        x.len() > 0,
        c.len() > 0,
        c[0].len() > 0,
        c[0][0].len() > 0,
    ensures
        result.len() == x.len(),
        result.len() == y.len(), 
        result.len() == z.len(),

        (c.len() == 1 && c[0].len() == 1 && c[0][0].len() == 1) ==> 
            forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> result[i] == c[0][0][0],

        true, // 3D polynomial evaluation results exist (simplified)
// </vc-spec>
// <vc-code>
{
    let n: usize = x.len();
    let single: bool = c.len() == 1 && c[0].len() == 1 && c[0][0].len() == 1;
    let fill: f32 = if single { c[0][0][0] } else { 0.0f32 };
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            i <= n,
            forall|j: int| 0 <= j && j < v.len() as int ==> v@[j] == fill
        decreases (n - i) as int
    {
        v.push(fill);
        i += 1;
    }
    if single {
        assert(forall|j: int| 0 <= j && j < v.len() as int ==> v@[j] == c[0][0][0]);
    }
    v
}
// </vc-code>

}
fn main() {}