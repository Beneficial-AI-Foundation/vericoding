// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): index from end for length n and position i */
spec fn rev_index(n: nat, i: nat) -> int { n as int - 1 - i as int }
/* helper modified by LLM (iteration 3): bounds of rev_index when i < n */
proof fn lemma_rev_index_bounds(n: nat, i: nat)
    requires
        i < n,
    ensures
        0 <= rev_index(n, i) && rev_index(n, i) < n as int
{
}

// </vc-helpers>

// <vc-spec>
fn reverse_string(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> result@[i] == s@[s@.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build reversed vector by pushing elements from the end with loop invariants ensuring the spec */
    let n: usize = s.len();
    let mut out: Vec<char> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out.len() == i,
            s@.len() == n as int,
            forall|j: int| 0 <= j && j < i as int ==> out@[j] == s@[(n as int) - 1 - j],
        decreases n as int - i as int
    {
        assert(i + 1 <= n);
        let j: usize = n - i - 1;
        assert(j < n);
        let ch = s[j];
        out.push(ch);
        i += 1;
        proof {
            assert(out@[i as int - 1] == ch);
            assert((j as int) == (n as int) - 1 - ((i as int) - 1));
            assert(ch == s@[j as int]);
        }
    }
    assert(i == n);
    assert(s@.len() == n as int);
    out
}
// </vc-code>

}
fn main() {}