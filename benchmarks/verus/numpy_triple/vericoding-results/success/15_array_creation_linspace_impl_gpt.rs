// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_lt_one_implies_zero(i: int) ensures 0 <= i && i < 1 ==> i == 0 { }
// </vc-helpers>

// <vc-spec>
fn linspace(start: f32, stop: f32, num: usize) -> (result: Vec<f32>)
    requires num > 0,
    ensures
        result.len() == num,
        result[0] == start,
        (num == 1 ==> forall|i: int| 0 <= i < num ==> result[i] == start),
        (num > 1 ==> result[num - 1] == stop)
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<f32> = Vec::new();
    if num == 1 {
        v.push(start);
        v
    } else {
        v.push(start);
        assert(num >= 2);
        let upper = num - 1;
        let mut i: usize = 1;
        while i < upper
            invariant
                2 <= num,
                1 <= i <= upper,
                upper == num - 1,
                v.len() == i,
                v[0] == start
            decreases upper - i
        {
            v.push(start);
            i += 1;
        }
        v.push(stop);
        v
    }
}
// </vc-code>

}
fn main() {}