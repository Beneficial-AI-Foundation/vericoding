// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &Vec<i8>) -> (result: bool)
    ensures result <==> forall|i: int| 0 <= i < a@.len() ==> (is_odd(i) ==> is_odd(a@[i] as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}