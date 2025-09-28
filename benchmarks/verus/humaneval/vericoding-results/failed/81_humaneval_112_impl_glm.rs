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
/* helper modified by LLM (iteration 2): added contains_char to replace unsupported slice::contains */
fn contains_char(c: &Vec<char>, ch: char) -> (result: bool)
    ensures
        result == exists|i: int| 0 <= i < c@.len() && c@[i] == ch,
{
    let mut found = false;
    for i in 0..c.len()
        invariant
            !found ==> forall|j: int| 0 <= j < i ==> c@[j] != ch,
            found ==> exists|j: int| 0 <= j < i && c@[j] == ch,
    {
        if c[i] == ch {
            found = true;
        }
    }
    found
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
/* code modified by LLM (iteration 5): added decreases clauses to both while loops */
{
    let mut filtered = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            filtered@ == filter_chars(s@.subrange(0, i as int), c@),
        decreases s.len() - i
    {
        if !contains_char(&c, s[i]) {
            filtered.push(s[i]);
        }
        i += 1;
    }

    let mut is_palindrome = true;
    let n = filtered.len();
    let mut j = 0;
    while j < n/2
        invariant
            0 <= j <= n/2,
            n-1-j >= 0,
            is_palindrome ==> (forall|k: int| 0 <= k < j ==> filtered@[k] == filtered@[n-1-k]),
        decreases n/2 - j
    {
        if filtered[j] != filtered[n-1-j] {
            is_palindrome = false;
            break;
        }
        j += 1;
    }

    (filtered, is_palindrome)
}
// </vc-code>


}

fn main() {}