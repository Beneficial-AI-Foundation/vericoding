// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define exists_in_prefix and lemma with correct nat->int indexing */
spec fn exists_in_prefix(s: Seq<i32>, k: i32, n: nat) -> bool {
    exists|j: int| 0 <= j < n && s[j] == k
}

proof fn lemma_exists_prefix_push(s: Seq<i32>, k: i32, n: nat)
    requires
        n < s.len(),
    ensures
        exists_in_prefix(s, k, n + 1) == (exists_in_prefix(s, k, n) || s[n as int] == k)
{ }
// </vc-helpers>

// <vc-spec>
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)

    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement linear scan with nat-usize conversion and use lemma to maintain invariant */
    let n: usize = arr.len();
    let mut i: usize = 0;
    let mut found: bool = false;

    while i < n
        invariant
            n == arr.len(),
            i <= n,
            found == exists_in_prefix(arr@, k, i as nat),
        decreases n - i
    {
        let ai = arr[i];
        let new_found = found || (ai == k);
        proof {
            assert((i as nat) < arr@.len()) by { };
            assert(arr@[i as int] == ai);
            lemma_exists_prefix_push(arr@, k, i as nat);
        }
        found = new_found;
        i = i + 1;
    }
    found
}
// </vc-code>

}
fn main() {}