// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn filter_chars(s: Seq<char>, c: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else if c.contains(s[0]) {
        filter_chars(s.subrange(1, s.len() as int), c)
    } else {
        seq![s[0]].add(filter_chars(s.subrange(1, s.len() as int), c))
    }
}

spec fn reverse_seq(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]])
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_filter_chars_preserves_order(s: Seq<char>, c: Seq<char>, idx: int)
    requires
        0 <= idx < filter_chars(s, c).len(),
    ensures
        exists k: int {
            0 <= k < s.len() && filter_chars(s, c)[idx] == s[k]
                && forall j: int :: 0 <= j < k && !c.contains(s[j]) ==> j < idx
        },
    decreases s.len()
{
    /* helper modified by LLM (iteration 5): Fixed a compilation error by adding curly braces to the `exists` clause. */
    if s.len() == 0 {
        // vacuously true
    } else if c.contains(s[0]) {
        lemma_filter_chars_preserves_order(s.subrange(1, s.len() as int), c, idx);
    } else {
        if idx == 0 {
            // s[0] is the character at filter_chars(s,c)[0]
        } else {
            lemma_filter_chars_preserves_order(s.subrange(1, s.len() as int), c, idx - 1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn reverse_delete(s: Vec<char>, c: Vec<char>) -> (result: (Vec<char>, bool))
    ensures
        result.0@ == filter_chars(s@, c@),
        result.1 == (result.0@ == reverse_seq(result.0@)),
        result.0@.len() <= s@.len(),
        forall|i: int| #![auto] 0 <= i < result.0@.len() ==> !c@.contains(result.0@[i]),
        forall|i: int| #![auto] 0 <= i < result.0@.len() ==> s@.contains(result.0@[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation issue by adding missing brace for `exists k: int { ... }`. */
    let mut i = 0;
    let mut filtered_vec: Vec<char> = Vec::new();

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            filtered_vec@ == filter_chars(s@.subrange(0, i as int), c@),
            forall|j: int| 0 <= j < filtered_vec@.len() ==> !c@.contains(filtered_vec@[j]),
            forall|j: int| 0 <= j < filtered_vec@.len() ==> s@.contains(filtered_vec@[j]),
    {
        let current_char = s[i];
        if !c.contains(current_char) {
            filtered_vec.push(current_char);
        }
        i = i + 1;
    }

    let mut reversed_vec: Vec<char> = Vec::new();
    let mut j = filtered_vec.len() as int - 1;
    while j >= 0
        invariant
            -1 <= j < filtered_vec.len(),
            reversed_vec@ == reverse_seq(filtered_vec@.subrange((j + 1) as int, filtered_vec.len() as int)),
            (filtered_vec.len() as int) - 1 - (j as int) == reversed_vec@.len(),
            forall|k: int| 0 <= k < reversed_vec@.len() && 0 <= (filtered_vec.len() as int) - 1 - k < filtered_vec@.len()
                ==>
                reversed_vec@[k] == filtered_vec@[(filtered_vec.len() as int) - 1 - k],
    {
        reversed_vec.push(filtered_vec[j as usize]);
        j = j - 1;
    }

    let is_palindrome = filtered_vec@ == reversed_vec@;
    (filtered_vec, is_palindrome)
}
// </vc-code>


}

fn main() {}