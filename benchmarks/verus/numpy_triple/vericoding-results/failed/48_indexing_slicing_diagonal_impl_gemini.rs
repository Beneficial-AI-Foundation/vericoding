// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn diagonal(a: Vec<Vec<f64>>, offset: i32) -> (result: Vec<f64>)
    requires 
        a.len() > 0,
        a.len() > 0 ==> a[0].len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len(),
        if offset >= 0 { 
            offset as int <= a[0].len() as int
        } else { 
            (-offset) as int <= a.len() as int
        },
    ensures
        result.len() == (if offset >= 0 { 
            if a.len() as int <= (a[0].len() as int - offset as int) { a.len() as int } else { a[0].len() as int - offset as int }
        } else { 
            if (a.len() as int + (-offset) as int) <= a[0].len() as int { a.len() as int + (-offset) as int } else { a[0].len() as int }
        }) as usize,
        forall|i: int| 0 <= i < result.len() ==> {
            if offset >= 0 {
                #[trigger] result[i] == a[i][i + offset as int]
            } else {
                #[trigger] result[i] == a[i + (-offset) as int][i]
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [Added `decreases` clauses to fix termination errors.] */
    let mut result = Vec::new();
    let m = a.len();
    let n = a[0].len();

    if offset >= 0 {
        let off = offset as usize;
        let len = if m <= n - off { m } else { n - off };
        let mut i: usize = 0;
        while i < len
            invariant
                a.len() > 0,
                a[0].len() > 0,
                forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j].len() == a[0].len(),
                offset >= 0,
                offset as int <= a[0].len() as int,
                len as int == min(a.len() as int, a[0].len() as int - offset as int),
                i <= len,
                result.len() == i,
                forall|k: int| 0 <= k < i as int ==> #[trigger] result.view()[k] == a.view()[k][k + offset as int],
            decreases len - i
        {
            let val = a[i][i + off];
            result.push(val);
            i = i + 1;
        }
    } else {
        let neg_off = -offset;
        let neg_off_usize = neg_off as usize;
        let len = if n <= m - neg_off_usize { n } else { m - neg_off_usize };

        let mut i: usize = 0;
        while i < len
            invariant
                a.len() > 0,
                a[0].len() > 0,
                forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j].len() == a[0].len(),
                offset < 0,
                (-offset) as int <= a.len() as int,
                len as int == min(a[0].len() as int, a.len() as int - (-offset) as int),
                i <= len,
                result.len() == i,
                forall|k: int| 0 <= k < i as int ==> #[trigger] result.view()[k] == a.view()[k + (-offset) as int][k],
            decreases len - i
        {
            let val = a[i + neg_off_usize][i];
            result.push(val);
            i = i + 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}