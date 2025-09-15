// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(x: i32) -> bool {
    x % 2 != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_first_odd(a: &Vec<i32>) -> (result: Option<usize>)
    requires a.len() > 0,
    ensures
        match result {
            Some(idx) => idx < a.len() && is_odd(a[idx as int]) &&
                forall|j: int| 0 <= j < idx ==> !is_odd(a[j]),
            None => forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i]),
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed compilation error by avoiding 'as int' cast in exec code and using direct modulo check on exec element instead of spec function call on sequence element. */
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len() as int,
            forall|j: int| 0 <= j < i as int ==> !is_odd(a@[j]),
        decreases
            (a.len() as int - i as int)
    {
        if a[i] % 2 != 0 {
            return Some(i);
        }
        i += 1;
    }
    None
}
// </vc-code>

}
fn main() {}