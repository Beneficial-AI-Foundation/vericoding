// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn transform_element(value: int, index: int) -> int
{
    if index % 3 == 0 { 
        value * value
    } else if index % 4 == 0 { 
        value * value * value
    } else { 
        value
    }
}

spec fn sum_partial(lst: Seq<int>, n: int) -> int
    decreases n
    when 0 <= n <= lst.len()
{
    if n == 0 { 
        0
    } else { 
        sum_partial(lst, n-1) + transform_element(lst[n-1], n-1)
    }
}

spec fn sum_transformed(lst: Seq<int>) -> int
{
    sum_partial(lst, lst.len() as int)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lambda syntax in seq_to_int */
spec fn seq_to_int(s: Seq<i8>) -> Seq<int> {
    s.map(|i, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn sum_squares(lst: Vec<i8>) -> (result: i8)
    ensures result as int == sum_transformed(seq_to_int(lst@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed assume statements, added proper overflow bounds */
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            sum as int == sum_partial(seq_to_int(lst@), i as int),
            forall|j: int| 0 <= j < i ==> {
                let v = lst@[j] as int;
                let t = transform_element(v, j);
                i8::MIN <= t <= i8::MAX
            },
        decreases lst.len() - i
    {
        let val = lst[i];
        let val_int = val as int;
        
        let transformed_int: int = if i % 3 == 0 {
            val_int * val_int
        } else if i % 4 == 0 {
            val_int * val_int * val_int
        } else {
            val_int
        };
        
        // Verify bounds
        assert(i8::MIN <= transformed_int <= i8::MAX) by {
            if i % 3 == 0 {
                assert(-128 <= val_int <= 127);
                assert(val_int * val_int <= 127 * 127);
                assert(val_int * val_int <= 16129);
            } else if i % 4 == 0 {
                assert(-128 <= val_int <= 127);
                if val_int >= 0 {
                    assert(val_int * val_int * val_int <= 127 * 127 * 127);
                } else {
                    assert(val_int * val_int * val_int >= -128 * 128 * 128);
                }
            }
        }
        
        let transformed = transformed_int as i8;
        
        assert(i8::MIN <= (sum as int + transformed as int) <= i8::MAX);
        sum = sum + transformed;
        
        i = i + 1;
    }
    
    sum
}
// </vc-code>


}

fn main() {}