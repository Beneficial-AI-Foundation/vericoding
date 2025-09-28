// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_letter(s: Seq<char>) -> bool
{
    exists|i: int| 0 <= i < s.len() && (('A' <= s[i] && s[i] <= 'Z') || ('a' <= s[i] && s[i] <= 'z'))
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s 
    } else { 
        s.subrange(s.len() as int - 1, s.len() as int).add(reverse_string(s.subrange(0, s.len() as int - 1)))
    }
}

spec fn swap_case(c: char) -> char
{
    if 'A' <= c && c <= 'Z' { 
        ((c as u32 + 32) as char)
    } else if 'a' <= c && c <= 'z' { 
        ((c as u32 - 32) as char)
    } else { 
        c 
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma linking reverse_string index to original index */
proof fn reverse_string_index(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        reverse_string(s).index(i) == s.index(s.len() - 1 - i),
    decreases
        s.len()
{
    // s.len() > 0 because 0 <= i < s.len()
    assert(s.len() > 0);
    let n: int = s.len() as int;
    // Unfold reverse_string for non-empty s
    assert(reverse_string(s) == s.subrange(n - 1, n).add(reverse_string(s.subrange(0, n - 1))));
    if i == 0 {
        // index 0 comes from the first (single-element) subrange
        assert(reverse_string(s).index(0) == s.subrange(n - 1, n).index(0));
        assert(s.subrange(n - 1, n).index(0) == s.index(n - 1));
    } else {
        // i >= 1: element comes from the tail reverse_string(s.subrange(0,n-1)) at index i-1
        let tail = s.subrange(0, n - 1);
        reverse_string_index(tail, i - 1);
        // join indexing: (single.add(tail_rev)).index(i) == tail_rev.index(i-1) for i >= 1
        assert(reverse_string(s).index(i) == reverse_string(tail).index(i - 1));
        assert(reverse_string(tail).index(i - 1) == tail.index(tail.len() - 1 - (i - 1)));
        assert(tail.index(tail.len() - 1 - (i - 1)) == s.index(n - 1 - i));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    ensures (if has_letter(s@) {
        result@.len() == s@.len() && 
        (forall|i: int| 0 <= i < s@.len() ==> result@[i] == swap_case(s@[i]))
    } else {
        result@ == reverse_string(s@)
    }) && result@.len() == s@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement solve for two branches (swap-case or reverse) */
    let n: int = s@.len() as int;
    if has_letter(s@) {
        let mut result: Vec<char> = Vec::new();
        let mut i: int = 0 as int;
        while i < n
            invariant
                0 <= i <= n,
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> result@.index(j) == swap_case(s@.index(j)),
            decreases
                n - i
        {
            result.push(swap_case(s@.index(i)));
            i = i + (1 as int);
        }
        result
    } else {
        let mut result: Vec<char> = Vec::new();
        let mut k: int = 0 as int;
        while k < n
            invariant
                0 <= k <= n,
                result@.len() == k,
                forall|j: int| 0 <= j < k ==> result@.index(j) == reverse_string(s@).index(j),
            decreases
                n - k
        {
            reverse_string_index(s@, k);
            result.push(s@.index(n - 1 - k));
            k = k + (1 as int);
        }
        result
    }
}

// </vc-code>


}

fn main() {}