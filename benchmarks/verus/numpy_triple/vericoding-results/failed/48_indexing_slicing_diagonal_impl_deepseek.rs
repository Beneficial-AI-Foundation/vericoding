// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ensures conditions and preconditions */
proof fn helper_lemma_offset_positive(a: Seq<Seq<f64>>, offset: int, i: int)
    requires
        offset >= 0,
        0 <= i < (if a.len() <= (a[0].len() - offset) { a.len() } else { a[0].len() - offset })
    ensures
        i < a.len(),
        i + offset < a[0].len()
{
    assert(i + offset >= 0);
}

proof fn helper_lemma_offset_negative(a: Seq<Seq<f64>>, offset: int, i: int)
    requires
        offset < 0,
        0 <= i < (if (a.len() + (-offset)) <= a[0].len() { a.len() + (-offset) } else { a[0].len() })
    ensures
        i + (-offset) < a.len(),
        i < a[0].len()
{
    assert(i + (-offset) >= 0);
}
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
/* code modified by LLM (iteration 5): Fixed arithmetic operations and indices */
{
    let mut result = Vec::new();
    let len = if offset >= 0 {
        let a_len_int = a.len() as int;
        let a0_len_int = a[0].len() as int;
        let offset_int = offset as int;
        
        if a_len_int <= (a0_len_int - offset_int) {
            a_len_int as usize
        } else {
            (a0_len_int - offset_int) as usize
        }
    } else {
        let a_len_int = a.len() as int;
        let a0_len_int = a[0].len() as int;
        let offset_int = offset as int;
        let neg_offset = -offset_int;
        
        if (a_len_int + neg_offset) <= a0_len_int {
            (a_len_int + neg_offset) as usize
        } else {
            a0_len_int as usize
        }
    };
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if offset >= 0 {
                    #[trigger] result[j] == a[j][j + offset as usize]
                } else {
                    #[trigger] result[j] == a[j + (-offset) as usize][j]
                }
            }
        decreases len - i
    {
        proof {
            if offset >= 0 {
                helper_lemma_offset_positive(a@.map(|j: int, v: Vec<f64>| v@), offset as int, i as int);
            } else {
                helper_lemma_offset_negative(a@.map(|j: int, v: Vec<f64>| v@), offset as int, i as int);
            }
        }
        
        let value = if offset >= 0 {
            a[i][i + offset as usize]
        } else {
            a[i + (-offset) as usize][i]
        };
        result.push(value);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}