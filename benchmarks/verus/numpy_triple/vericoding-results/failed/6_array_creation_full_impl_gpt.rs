// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove pairwise equality from uniform equality up to n */
proof fn lemma_all_equal_implies_pairwise<T>(s: Seq<T>, n: int, x: T)
    requires
        0 <= n <= s.len(),
        forall|i: int| 0 <= i < n ==> s[i] == x,
    ensures
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> s[i] == s[j]
{
    assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n implies s[i] == s[j] by {
        if 0 <= i < n && 0 <= j < n {
            assert(s[i] == x);
            assert(s[j] == x);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn full<T>(n: usize, fill_value: T) -> (result: Vec<T>)
    ensures 
        result.len() == n,

        forall|i: int| 0 <= i < n ==> result[i] == fill_value,

        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result[i] == result[j],

        n > 0 ==> result[0] == fill_value,
        n > 0 ==> result[(n-1) as int] == fill_value,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fill vector of length n by cloning fill_value and prove uniform and pairwise equality */
    let mut v: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            i <= n,
            forall|k: int| 0 <= k < i ==> v[k] == fill_value,
        decreases (n as int) - (i as int)
    {
        v.push(fill_value.clone());
        i = i + 1;
    }
    proof {
        lemma_all_equal_implies_pairwise::<T>(v@, n as int, fill_value);
    }
    if n > 0usize {
        assert(v[0] == fill_value);
        assert(v[(n - 1) as int] == fill_value);
    }
    v
}
// </vc-code>

}
fn main() {}