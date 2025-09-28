// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(l: Seq<int>) -> bool
{
    true
}

spec fn correct_output(l: Seq<int>, result: Seq<int>) -> bool
{
    result.len() == l.len() && 
    forall|i: int| 0 <= i < l.len() ==> result[i] == l[i] + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed predicate syntax by changing pred to spec fn */
spec fn can_increment_i8(x: i8) -> bool
{
    x < 127
}
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(l@.map(|i: int, x: i8| x as int))
    ensures correct_output(l@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow and assertion issues by using Vec::with_capacity and proper casting */
    let mut result = Vec::<i8>::with_capacity(l.len());
    let mut i = 0;
    while i < l.len()
        invariant
            i <= l.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (l@[j] as int) + 1,
        decreases l.len() - i
    {
        let incremented = (l[i] as i32 + 1) as i8;
        result.push(incremented);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}