// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn diagonal(a: Vec<Vec<f64>>, offset: i32) -> (result: Vec<f64>)
    requires 
        a@.len() > 0,
        a@.len() > 0 ==> a@[0].len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> #[trigger] a@[i].len() == a@[0].len(),
        if offset >= 0 { 
            offset as int <= a@[0].len() as int
        } else { 
            (-offset) as int <= a@.len() as int
        },
    ensures
        result@.len() == (if offset >= 0 { 
            if a@.len() as int <= (a@[0].len() as int - offset as int) { a@.len() as int } else { a@[0].len() as int - offset as int }
        } else { 
            if (a@.len() as int + (-offset) as int) <= a@[0].len() as int { a@.len() as int + (-offset) as int } else { a@[0].len() as int }
        }) as usize,
        forall|i: int| 0 <= i < result@.len() ==> {
            if offset >= 0 {
                #[trigger] result@[i] == a@[i][i + offset as int]
            } else {
                #[trigger] result@[i] == a@[i + (-offset) as int][i]
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed bounds checks and max_len calculation for negative offset case */
    let mut result: Vec<f64> = Vec::new();
    
    if offset >= 0 {
        let offset_nat = offset as usize;
        let max_len = if a.len() <= (a[0].len() - offset_nat) { 
            a.len() 
        } else { 
            a[0].len() - offset_nat 
        };
        
        let mut i: usize = 0;
        while i < max_len
            invariant
                i <= max_len,
                max_len <= a@.len(),
                max_len <= a@[0].len() - offset as int,
                offset >= 0,
                offset as int <= a@[0].len() as int,
                a@.len() > 0,
                forall|k: int| 0 <= k < a@.len() ==> a@[k].len() == a@[0].len(),
                max_len == (if a@.len() as int <= (a@[0].len() as int - offset as int) { a@.len() as int } else { a@[0].len() as int - offset as int }) as usize,
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[j][j + offset as int],
            decreases max_len - i
        {
            assert(i < a@.len());
            assert(i + offset_nat < a@[i].len());
            result.push(a[i][i + offset_nat]);
            i = i + 1;
        }
    } else {
        let neg_offset = ((-offset) as usize);
        let max_len = if (a.len() - neg_offset) <= a[0].len() { 
            a.len() - neg_offset 
        } else { 
            a[0].len() 
        };
        
        let mut i: usize = 0;
        while i < max_len
            invariant
                i <= max_len,
                max_len <= a@[0].len(),
                max_len + neg_offset <= a@.len(),
                offset < 0,
                (-offset) as int <= a@.len() as int,
                a@.len() > 0,
                forall|k: int| 0 <= k < a@.len() ==> a@[k].len() == a@[0].len(),
                max_len == (if (a@.len() as int - neg_offset as int) <= a@[0].len() as int { a@.len() as int - neg_offset as int } else { a@[0].len() as int }) as usize,
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[j + neg_offset as int][j],
            decreases max_len - i
        {
            assert(i + neg_offset < a@.len());
            assert(i < a@[i + neg_offset].len());
            result.push(a[i + neg_offset][i]);
            i = i + 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}