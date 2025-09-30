// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_even_at_index_even(lst: &Vec<i32>) -> (result: bool)
    ensures result <==> (forall|i: int| 0 <= i < lst.len() ==> (is_even(i) ==> is_even(lst[i] as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error in invariant by using correct sequence access syntax */
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < (i as int) ==> (is_even(j) ==> is_even(lst@[j] as int)),
        decreases lst.len() - i
    {
        if i % 2 == 0 {
            let val = lst[i];
            if val % 2 != 0 {
                return false;
            }
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}