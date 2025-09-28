// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define a well-typed palindrome predicate using nat casts for indices */
spec fn palindrome_prop_casted(x: Seq<char>) -> bool {
    forall|i: int| 0 <= i < x.len() as int ==> #[trigger] x[i as nat] == x[(x.len() as int - 1 - i) as nat]
}

// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute palindrome property using well-typed indices and return it */
    let r = forall|i: int| 0 <= i < x.len() as int ==> #[trigger] x[i as nat] == x[(x.len() as int - 1 - i) as nat];
    r
}
// </vc-code>

}
fn main() {}