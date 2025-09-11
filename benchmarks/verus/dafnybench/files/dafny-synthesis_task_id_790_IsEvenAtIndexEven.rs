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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}