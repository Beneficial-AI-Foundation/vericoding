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
proof fn push_preserves_relations<T>(vec: &mut Vec<T>, value: T, i: int)
    requires
        old(vec)@.len() == i,
        i >= 0,
    ensures
        vec@.len() == i + 1,
        vec@[i] == value,
        forall|j: int| 0 <= j < i ==> vec@[j] == old(vec)@[j],
{
    vec.push(value);
}
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(l@.map(|i: int, x: i8| x as int))
    ensures correct_output(l@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and loop invariant */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == l@[j] as int + 1,
        decreases l.len() - i
    {
        let current = l[i];
        proof {
            push_preserves_relations(&mut result, current + 1, i as int);
        }
        let new_val = (current as i16 + 1) as i8;
        result.push(new_val);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}