use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn cube_def(i: int)
    ensures
        i * i * i == (i * i) * i,
{
}

proof fn cube_monotonic(i: int, j: int)
    requires
        i <= j,
    ensures
        i * i * i <= j * j * j,
{
    if i >= 0 {
        assert(i * i <= j * j) by {
            assert(i <= j);
        };
        assert((i * i) * i <= (j * j) * j) by {
            assert(i <= j);
        };
    } else if j <= 0 {
        assert(j * j <= i * i) by {
            assert(i <= j);
        };
        assert((j * j) * j <= (i * i) * i) by {
            assert(j <= i);
        };
    } else {
        // i < 0 < j
        assert(i * i * i < 0);
        assert(0 < j * j * j);
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    // post-conditions-start
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    let mut count: usize = 0;
    while count < len
        invariant
            res@.len() == count,
            forall|k: int| 0 <= k && k < count ==> res@[k] == k * k * k,
            count <= len,
    {
        res.push((count as i32) * (count as i32) * (count as i32));
        count = count + 1;
    }
    res
}
// </vc-code>

fn main() {}
}