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
    s.map(|i, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn sum_squares(lst: Vec<i8>) -> (result: i8)
    ensures result as int == sum_transformed(seq_to_int(lst@))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}