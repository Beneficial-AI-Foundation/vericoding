// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added bounds checking helper functions */
fn bounds_check_positive_offset(a: &Vec<Vec<f64>>, i: usize, offset: i32) -> (res: bool)
    requires
        offset >= 0,
        a@.len() > 0,
        a@[0].len() > 0,
        forall|k: int| 0 <= k < a@.len() ==> a@[k].len() == a@[0].len(),
    ensures
        res == (i < a@.len() && (i + offset as usize) < a@[0].len()),
{
    i < a.len() && (i + offset as usize) < a[0].len()
}

fn bounds_check_negative_offset(a: &Vec<Vec<f64>>, i: usize, neg_offset: usize) -> (res: bool)
    requires
        a@.len() > 0,
        a@[0].len() > 0,
        forall|k: int| 0 <= k < a@.len() ==> a@[k].len() == a@[0].len(),
    ensures
        res == ((i + neg_offset) < a@.len() && i < a@[0].len()),
{
    (i + neg_offset) < a.len() && i < a[0].len()
}
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
    /* code modified by LLM (iteration 5): fixed array indexing syntax */
    let mut result = Vec::new();
    
    if offset >= 0 {
        let offset_val = offset as usize;
        let max_len = if a.len() <= (a[0].len() - offset_val) { a.len() } else { a[0].len() - offset_val };
        
        let mut i = 0;
        while i < max_len
            invariant
                i <= max_len,
                max_len <= a@.len(),
                offset_val <= a@[0].len(),
                max_len <= a@[0].len() - offset_val,
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> (0 <= j < a@.len() && 0 <= j + offset as int < a@[0]@.len()),
                forall|j: int| #![auto] 0 <= j < i ==> result@[j] == a@[j]@[j + offset as int],
            decreases max_len - i
        {
            assert(i < a.len());
            assert((i + offset_val) < a[0].len());
            result.push(a[i][i + offset_val]);
            i += 1;
        }
    } else {
        let neg_offset_i32 = -offset;
        assert(neg_offset_i32 >= 0);
        let neg_offset = neg_offset_i32 as usize;
        let max_len = if a.len() >= neg_offset && (a.len() - neg_offset) <= a[0].len() { a.len() - neg_offset } else { a[0].len() };
        
        let mut i = 0;
        while i < max_len
            invariant
                i <= max_len,
                neg_offset <= a@.len(),
                max_len <= a@[0]@.len(),
                max_len <= a@.len() - neg_offset,
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> (0 <= j + neg_offset as int < a@.len() && 0 <= j < a@[0]@.len()),
                forall|j: int| #![auto] 0 <= j < i ==> result@[j] == a@[j + neg_offset as int]@[j],
            decreases max_len - i
        {
            assert(i + neg_offset < a.len());
            assert(i < a[0].len());
            result.push(a[i + neg_offset][i]);
            i += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}