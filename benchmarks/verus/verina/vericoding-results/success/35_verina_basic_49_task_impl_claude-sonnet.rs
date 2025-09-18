// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(x: i32) -> bool {
    x % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added exec function to call spec function from exec code */
exec fn is_odd_exec(x: i32) -> (result: bool)
    ensures result == is_odd(x)
{
    x % 2 != 0
}
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
    /* code modified by LLM (iteration 4): added decreases clause to fix compilation error */
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> !is_odd(a[j]),
        decreases a.len() - i
    {
        if is_odd_exec(a[i]) {
            return Some(i);
        }
        i += 1;
    }
    None
}
// </vc-code>

}
fn main() {}