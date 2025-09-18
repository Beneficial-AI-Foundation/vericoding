// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed function signatures and parameter types */
proof fn fromiter_spec_lemma<T: Copy>(n: nat, iter: spec_fn(nat) -> T)
    ensures
        forall|i: nat| i < n ==> #[trigger] fromiter_spec(n, iter)[i] == iter(i)
{
    if n > 0 {
        fromiter_spec_lemma(n - 1, iter);
    }
}

spec fn fromiter_spec<T>(n: nat, iter: spec_fn(nat) -> T) -> Seq<T>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        fromiter_spec(n - 1, iter).push(iter(n - 1))
    }
}
// </vc-helpers>

// <vc-spec>
fn fromiter<T: Copy>(n: usize, iter: spec_fn(usize) -> T) -> (result: Vec<T>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == iter(i as usize)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type conversions and verification conditions */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i as nat,
            forall|j: nat| j < i ==> result@[j] == iter(j),
            decreases n - i
    {
        result.push(iter(i));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}