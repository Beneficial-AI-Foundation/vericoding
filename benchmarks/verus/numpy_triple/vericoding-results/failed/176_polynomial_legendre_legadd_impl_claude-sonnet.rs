// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed helper function to return boolean value instead of using proof block */
fn can_add_i8(a: i8, b: i8) -> (result: bool)
    ensures result == (-128 <= (a as int) + (b as int) <= 127)
{
    let a_int = a as int;
    let b_int = b as int;
    let sum = a_int + b_int;
    -128 <= sum && sum <= 127
}

fn add_i8_safe(a: i8, b: i8) -> (result: i8)
    requires can_add_i8(a, b)
    ensures (result as int) == (a as int) + (b as int)
{
    a + b
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
    /* code modified by LLM (iteration 5): simplified overflow checking logic */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < max_len
        invariant
            i <= max_len,
            max_len == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let val1: int = if j < c1@.len() { c1@[j] as int } else { 0 };
                let val2: int = if j < c2@.len() { c2@[j] as int } else { 0 };
                #[trigger] result@[j] as int == val1 + val2
            },
        decreases max_len - i
    {
        let val1: i8 = if i < c1.len() { c1[i] } else { 0 };
        let val2: i8 = if i < c2.len() { c2[i] } else { 0 };
        
        proof {
            let val1_int = val1 as int;
            let val2_int = val2 as int;
            assert(-128 <= val1_int <= 127);
            assert(-128 <= val2_int <= 127);
            assert(-256 <= val1_int + val2_int <= 254);
            assert(can_add_i8(val1, val2));
        }
        
        let sum = add_i8_safe(val1, val2);
        result.push(sum);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}