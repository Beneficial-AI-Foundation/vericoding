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
spec fn seq_to_int(s: Seq<i8>) -> Seq<int> {
    s.map(|i: int, x: i8| x as int)
}

proof fn transform_element_nonnegative()
    ensures
        forall |value: int, index: int| transform_element(value, index) >= 0,
{
    /* helper modified by LLM (iteration 5): Fixed missing parameter type annotation in lambda */
}
// </vc-helpers>

// <vc-spec>
fn sum_squares(lst: Vec<i8>) -> (result: i8)
    ensures result as int == sum_transformed(seq_to_int(lst@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error by removing @ from lst@ in assignment */
    let mut sum: i8 = 0;
    let mut index: usize = 0;
    let len = lst.len();
    
    while index < len
        invariant
            0 <= index <= len,
            sum as int == sum_partial(seq_to_int(lst@), index as int),
        decreases len - index
    {
        let value = lst[index];
        let transformed = if index % 3 == 0 {
            (value as i32 * value as i32) as i8
        } else if index % 4 == 0 {
            (value as i32 * value as i32 * value as i32) as i8
        } else {
            value
        };
        sum = (sum as i16 + transformed as i16) as i8;
        index = index + 1;
    }
    
    sum
}
// </vc-code>


}

fn main() {}