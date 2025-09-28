// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn legadd_helper(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let val1: int = if i < c1@.len() { c1@[i] as int } else { 0 };
            let val2: int = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == val1 + val2
        }
{
    let len1 = c1@.len();
    let len2 = c2@.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };
    let mut result = Vec::with_capacity(max_len as usize);
    
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i <= max_len,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let val1: int = if j < len1 { c1@[j] as int } else { 0 };
                let val2: int = if j < len2 { c2@[j] as int } else { 0 };
                result@[j] as int == val1 + val2
            },
        decreases max_len - i
    {
        let val1 = if i < len1 { c1@[i] } else { 0 };
        let val2 = if i < len2 { c2@[i] } else { 0 };
        result.push(val1 + val2);
        i += 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn legadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let val1: int = if i < c1@.len() { c1@[i] as int } else { 0 };
            let val2: int = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == val1 + val2
        }
// </vc-spec>
// <vc-code>
{
    legadd_helper(c1, c2)
}
// </vc-code>


}
fn main() {}