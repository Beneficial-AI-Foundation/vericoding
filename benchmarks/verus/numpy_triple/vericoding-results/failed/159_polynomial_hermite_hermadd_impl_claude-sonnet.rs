// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added overflow bounds to prevent arithmetic overflow */
fn get_or_zero(v: &Vec<i8>, i: usize) -> (result: i8)
    requires
        i < usize::MAX,
        v@.len() <= usize::MAX,
    ensures
        result as int == if i < v@.len() { v@[i as int] as int } else { 0 },
        -128 <= result as int <= 127,
{
    if i < v.len() {
        v[i]
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn hermadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==>
            result@[i] as int == (
                if i < c1@.len() && i < c2@.len() {
                    c1@[i] as int + c2@[i] as int
                } else if i < c1@.len() {
                    c1@[i] as int
                } else if i < c2@.len() {
                    c2@[i] as int
                } else {
                    0
                }
            ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed quantifier triggers with explicit trigger annotation */
    let len1 = c1.len();
    let len2 = c2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };
    
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if len1 >= len2 { len1 } else { len2 },
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int == {
                let expected_val = if j < len1 as int && j < len2 as int {
                    c1@[j] as int + c2@[j] as int
                } else if j < len1 as int {
                    c1@[j] as int
                } else if j < len2 as int {
                    c2@[j] as int
                } else {
                    0
                };
                expected_val
            } && -256 <= (if j < len1 as int && j < len2 as int {
                c1@[j] as int + c2@[j] as int
            } else if j < len1 as int {
                c1@[j] as int
            } else if j < len2 as int {
                c2@[j] as int
            } else {
                0
            }) <= 254,
        decreases max_len - i
    {
        let val1 = get_or_zero(&c1, i);
        let val2 = get_or_zero(&c2, i);
        
        let val = if i < len1 && i < len2 {
            val1 + val2
        } else if i < len1 {
            val1
        } else {
            val2
        };
        
        proof {
            assert(i < max_len);
            if i < len1 && i < len2 {
                assert(i < c1@.len() && i < c2@.len());
            }
        }
        
        result.push(val);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}