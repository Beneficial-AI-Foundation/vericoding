// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_all_equal_pairwise<T>(n: int, s: Seq<T>, val: T)
    requires
        0 <= n <= s.len(),
        forall|i: int| 0 <= i < n ==> s[i] == val,
    ensures
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> s[i] == s[j],
{
    assert forall|i: int, j: int|
        0 <= i < n && 0 <= j < n ==> s[i] == s[j] by
    {
        if 0 <= i && i < n && 0 <= j && j < n {
            assert(s[i] == val);
            assert(s[j] == val);
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
    let mut v: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == fill_value,
        decreases n - i
    {
        v.push(fill_value);
        i += 1;
    }
    proof {
        lemma_all_equal_pairwise(n as int, v@, fill_value);
    }
    v
}
// </vc-code>

}
fn main() {}