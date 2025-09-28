// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helpers_dummy() {
}

// </vc-helpers>

// <vc-spec>
fn right_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& (x1[i] >= 0 ==> result[i] == x1[i] / (1i32 << x2[i]))
            &&& (x1[i] < 0 ==> result[i] == x1[i] >> x2[i])
            &&& (x2[i] == 0 ==> result[i] == x1[i])
            &&& (x1[i] > 0 ==> result[i] >= 0)
            &&& (x1[i] < 0 ==> result[i] <= 0)
            &&& (x1[i] == 0 ==> result[i] == 0)
        }
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (x1[j] >= 0 ==> res[j] == x1[j] / (1i32 << x2[j]))
                &&& (x1[j] < 0 ==> res[j] == x1[j] >> x2[j])
                &&& (x2[j] == 0 ==> res[j] == x1[j])
                &&& (x1[j] > 0 ==> res[j] >= 0)
                &&& (x1[j] < 0 ==> res[j] <= 0)
                &&& (x1[j] == 0 ==> res[j] == 0)
            },
        decreases x1.len() - i
    {
        let s: i32 = x2[i];
        let xi: i32 = x1[i];
        let yi: i32 = if xi >= 0 { xi / (1i32 << s) } else { xi >> s };
        res.push(yi);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}