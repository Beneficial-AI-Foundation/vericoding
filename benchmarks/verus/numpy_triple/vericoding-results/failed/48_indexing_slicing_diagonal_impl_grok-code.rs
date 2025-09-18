// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Removed malformed assert, added proper assertions for array access bounds in proof blocks */
    let mut result = Vec::new();
    if offset >= 0 {
        let offset_us = offset as usize;
        let mut i = 0;
        proof {
            assert(offset as int <= a[0].len() as int);
        }
        while i < a.len() && (i as int + offset_us as int) < a[0].len() as int
            decreases a.len() - i
        {
            proof {
                assert(0 <= i as int < a.len() as int);
                assert(0 <= i as int + offset as int < a[0].len() as int);
            }
            result.push(a[i][i + offset_us]);
            i += 1;
        }
    } else {
        let neg_offset_us = ((-offset) as i64) as usize;
        let mut i = neg_offset_us;
        let neg_offset = (-offset) as int;
        proof {
            assert(neg_offset <= a.len() as int);
        }
        while i < a.len() && i >= neg_offset_us && (i as int - neg_offset_us as int) < a[0].len() as int
            decreases a.len() - i
        {
            proof {
                assert(0 <= i as int < a.len() as int);
                let j = i - neg_offset_us;
                assert(0 <= j as int < a[0].len() as int);
                assert(j as int == i as int - neg_offset);
            }
            result.push(a[i][i - neg_offset_us]);
            i += 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}