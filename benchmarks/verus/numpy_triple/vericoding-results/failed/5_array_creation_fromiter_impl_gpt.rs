// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec predicate encoding equality with iter */
spec fn is_iter_val<T>(i: usize, iter: spec_fn(usize) -> T, x: T) -> bool {
    x == iter(i)
}

/* helper modified by LLM (iteration 5): existence lemma to witness a value equal to iter(i) */
proof fn exists_equal_iter<T>(i: usize, iter: spec_fn(usize) -> T)
    ensures
        exists|x: T| is_iter_val(i, iter, x)
{
    assert(exists|x: T| is_iter_val(i, iter, x));
}

// </vc-helpers>

// <vc-spec>
fn fromiter<T: Copy>(n: usize, iter: spec_fn(usize) -> T) -> (result: Vec<T>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == iter(i as usize)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use a spec predicate inside choose to avoid PartialEq bound; build vector iteratively */
    let mut v: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == iter(j as usize),
        decreases n - i
    {
        proof { exists_equal_iter::<T>(i, iter); }
        let x: T = choose|x: T| is_iter_val(i, iter, x);
        v.push(x);
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}