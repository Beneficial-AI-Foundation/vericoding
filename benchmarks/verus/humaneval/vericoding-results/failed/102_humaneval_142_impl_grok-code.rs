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
/* helper modified by LLM (iteration 5): Keep the fix for the map function parameter name to correct syntax. */
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
/* code modified by LLM (iteration 5): Use i64 instead of i128 for sum_mut and v to resolve arithmetic overflow errors. */
    let mut sum_mut: i64 = 0;
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i as int,
            i as int <= lst.len() as int,
            sum_mut as int == sum_partial(seq_to_int(lst@), i as int),
            -128 <= sum_mut,
            sum_mut <= 127,
        decreases lst.len() - i,
    {
        let v: i64 = lst[i] as i64;
        let t: i64 = if i % 3 == 0 {
            v * v
        } else if i % 4 == 0 {
            v * v * v
        } else {
            v
        };
        sum_mut += t;
        i += 1;
    }
    let result = sum_mut as i8;
    result
}
// </vc-code>


}

fn main() {}