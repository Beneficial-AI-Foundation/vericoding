// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no helpers needed] */
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [use forall spec and fix types] */
    (forall|i: int| 0 <= i < x.len() ==> 
        #[trigger] x[i] == x[x.len() as int - 1 - i])
}
// </vc-code>

}
fn main() {}