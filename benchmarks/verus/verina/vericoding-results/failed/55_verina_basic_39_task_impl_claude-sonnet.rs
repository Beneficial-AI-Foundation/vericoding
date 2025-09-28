// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified spec function to match exact postcondition structure */
spec fn rotation_property(result: &Vec<i32>, l: &Vec<i32>, n: usize, i: usize) -> bool {
    forall|j: int| 0 <= j < i ==> {
        let len = l.len() as int;
        let rotated_index = ((j - n as int + len) % len) as int;
        #[trigger] result[j] == l[rotated_index]
    }
}
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: &Vec<i32>, n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> {
            let len = l.len() as int;
            let rotated_index = ((i - n as int + len) % len) as int;
            #[trigger] result[i] == l[rotated_index]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix helper call and prove postcondition preservation */
    if l.len() == 0 {
        return Vec::new();
    }
    
    let len = l.len();
    let effective_n = n % len;
    let mut result = Vec::with_capacity(len);
    
    let mut i = 0;
    while i < len
        invariant
            result.len() == i,
            i <= len,
            len == l.len(),
            effective_n < len,
            rotation_property(&result, l, effective_n, i),
        decreases len - i
    {
        proof {
            let len_int = len as int;
            let rotated_index_int = ((i as int - effective_n as int + len_int) % len_int);
            assert(0 <= rotated_index_int < len_int);
        }
        
        let source_index = if i >= effective_n {
            i - effective_n
        } else {
            len - effective_n + i
        };
        
        result.push(l[source_index]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}