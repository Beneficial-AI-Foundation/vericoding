// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation errors and corrected proof logic using div/mod lemmas. */
proof fn lemma_rotate_properties(l: Seq<int>, n: int)
    requires
        0 <= n,
        n < l.len(),
    ensures
        (l.subrange(n, l.len()) + l.subrange(0, n)).len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==>
            (l.subrange(n, l.len()) + l.subrange(0, n))@[i] == l@[((i + n) as nat % l.len()) as int],
{
    let second = l.subrange(n, l.len());
    let modulus = l.len() as nat;

    assert(l.len() > 0) by {
        requires(n >= 0 && n < l.len());
    };

    assert forall|i: int| 0 <= i < l.len() implies (second + l.subrange(0, n))@[i] == l@[((i + n) as nat % modulus) as int] by {
        if i < second.len() {
            // Case 1: 0 <= i < l.len() - n  ==>  n <= i + n < l.len()
            let index = (i + n) as nat;
            vstd::arithmetic::mod_internals::lemma_mod_of_nonneg_lt(index, modulus);
        } else {
            // Case 2: l.len() - n <= i < l.len()  ==>  l.len() <= i + n < 2 * l.len()
            let x = (i + n) as nat;
            vstd::arithmetic::div_mod::lemma_div_is_1(x, modulus);
            vstd::arithmetic::div_mod::lemma_div_mod_properties(x, modulus);
            assert(x % modulus == x - modulus);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No change needed, the compilation errors were in the helper proof. */
    lemma_rotate_properties(l, n);
    l.subrange(n, l.len()) + l.subrange(0, n)
}
// </vc-code>

}
fn main() {}