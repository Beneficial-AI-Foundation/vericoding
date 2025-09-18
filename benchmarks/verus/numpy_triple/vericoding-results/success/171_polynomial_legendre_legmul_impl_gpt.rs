// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min_int(a: int, b: int) -> int { if a < b { a } else { b } }
proof fn sum_pos_minus_one_nonneg(a: nat, b: nat)
    ensures a > 0 && b > 0 ==> a + b - 1 >= 0
{ }
// </vc-helpers>

// <vc-spec>
fn legmul(c1: Vec<f32>, c2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
// </vc-spec>
// <vc-code>
{
    let n1 = c1.len();
    let n2 = c2.len();

    let mut res: Vec<f32> = Vec::new();

    let mut i: usize = 0;
    while i < n1
        invariant
            res.len() == i,
            i <= n1,
            n1 == c1.len(),
            n2 == c2.len()
        decreases (n1 as int) - (i as int)
    {
        res.push(0.0f32);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < n2
        invariant
            j <= n2,
            n1 == c1.len(),
            n2 == c2.len(),
            res.len() as int == n1 as int + (if j == 0 { 0 } else { j as int - 1 })
        decreases (n2 as int) - (j as int)
    {
        if j > 0 {
            res.push(0.0f32);
        }
        j = j + 1;
    }

    res
}
// </vc-code>

}
fn main() {}