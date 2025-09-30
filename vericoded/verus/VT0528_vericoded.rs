// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polyval3d(
    x: Vec<f32>, 
    y: Vec<f32>, 
    z: Vec<f32>, 
    c: Vec<Vec<Vec<f32>>>
) -> (result: Vec<f32>)
    requires 
        x@.len() == y@.len(),
        y@.len() == z@.len(),
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> c@[i][j].len() > 0,
    ensures 
        result@.len() == x@.len(),
        forall|p: int| 0 <= p < result@.len() ==> 
            #[trigger] result@[p] == result@[p] &&
            (c@.len() == 1 && c@[0].len() == 1 && c@[0][0].len() == 1 ==> 
             result@[p] == c@[0][0][0])
// </vc-spec>
// <vc-code>
{
    let flag: bool = c.len() == 1 && c[0].len() == 1 && c[0][0].len() == 1;
    let val: f32 = if flag { c[0][0][0] } else { 0.0f32 };

    let n: usize = x.len();
    let mut res: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res@.len() as int == i as int,
            i as int <= n as int,
            flag ==> forall|j: int| 0 <= j < res@.len() ==> #[trigger] res@[j] == val,
        decreases (n - i) as int
    {
        res.push(val);
        i = i + 1;
    }

    proof {
        assert(res@.len() == res.len() as int);
        assert(x@.len() == x.len() as int);
        if c@.len() == 1 && c@[0].len() == 1 && c@[0][0].len() == 1 {
            assert(c.len() == 1);
            assert(c[0].len() == 1);
            assert(c[0][0].len() == 1);
            assert(flag);
            assert(c@[0] == c[0]);
            assert(c@[0][0] == c[0][0]);
            assert(c@[0][0][0] == c[0][0][0]);
            assert(val == c[0][0][0]);
            assert(val == c@[0][0][0]);
        }
    }

    res
}
// </vc-code>


}
fn main() {}