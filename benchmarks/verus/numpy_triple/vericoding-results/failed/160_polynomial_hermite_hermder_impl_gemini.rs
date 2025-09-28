// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [retained dummy helper, no complex helpers needed yet] */
spec fn dummy_h() -> bool { true }
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i8>, m: usize, scl: i8) -> (result: Vec<i8>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] as int == (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int)
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] as int == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int)
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [fixed compile error, removed verification bypasses] */
    if m >= c.len() {
        return Vec::new();
    }

    let mut temp_c = c;
    let mut j: usize = 0;
    while j < m
        invariant
            0 <= j <= m,
            m < c.len() ==> temp_c.len() as nat == c.len() as nat - (j as nat),
        decreases m - j
    {
        let n = temp_c.len();
        if n < 1 {
            break;
        }

        let mut new_c = Vec::with_capacity(n - 1);

        let mut i: usize = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                new_c.len() == i,
            decreases (n - 1) - i
        {
            let val = (scl as i64) * (2 * ((i as i64) + 1)) * (temp_c[i + 1] as i64);
            new_c.push(val as i8);
            i = i + 1;
        }
        temp_c = new_c;
        j = j + 1;
    }

    temp_c
}
// </vc-code>

}
fn main() {}