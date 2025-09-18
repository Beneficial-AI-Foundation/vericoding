// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate(a: &Vec<i32>, offset: int) -> (result: Vec<i32>)
    requires offset >= 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = (i + offset) % (a.len() as int);
            #[trigger] result[i] == a[src_idx]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use builtin conversion for int to usize */
    if a.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::with_capacity(a.len());
    let ghost len = a.len() as int;
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            len == a.len(),
            forall|j: int| 0 <= j < i ==> {
                let src_idx = (j + offset) % len;
                #[trigger] result[j] == a[src_idx]
            },
    {
        let ghost i_int = i as int;
        let ghost src_idx = (i_int + offset) % len;
        proof {
            assert(0 <= src_idx < len);
        }
        let src_usize = vstd::prelude::int_to_usize(src_idx);
        result.push(a[src_usize]);
    }
    
    result
}
// </vc-code>

}
fn main() {}