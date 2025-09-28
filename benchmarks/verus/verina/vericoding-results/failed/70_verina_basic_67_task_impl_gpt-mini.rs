// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): bounds and index helpers */

/* helper modified by LLM (iteration 5): proof that reversed index is within bounds for nat indices */
proof fn rev_index_in_bounds<T>(x: Seq<T>, i: nat)
    requires
        i < x.len()
{
    // i < x.len() implies len > 0 and the subtraction is within nat bounds
    assert(x.len() > 0);
    assert(x.len() - 1 - i < x.len());
}

/* helper modified by LLM (iteration 5): trivial proof that Seq length is non-negative */
proof fn len_nonneg<T>(s: Seq<T>) {
    assert(s.len() >= 0);
}

// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use nat quantifier and Seq.index to check palindrome */
    (forall|i: nat| i < x.len() ==> #[trigger] x.index(i) == x.index(x.len() - 1 - i))
}

// </vc-code>

}
fn main() {}