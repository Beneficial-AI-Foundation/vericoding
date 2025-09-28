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

proof fn reverse_seq_filter_commute(s: Seq<char>, c: Seq<char>)
    ensures
        reverse_seq(filter_chars(s, c)) == filter_chars(reverse_seq(s), c),
    decreases s.len()
{
    if s.len() == 0 {
        assert(reverse_seq(filter_chars(Seq::empty(), c)) == filter_chars(reverse_seq(Seq::empty()), c));
    } else {
        reverse_seq_filter_commute(s.subrange(1, s.len() as int), c);
        if c.contains(s[0]) {
            assert(filter_chars(s, c) == filter_chars(s.subrange(1, s.len() as int), c));
            assert(reverse_seq(filter_chars(s, c)) == reverse_seq(filter_chars(s.subrange(1, s.len() as int), c)));
            assert(reverse_seq(s) == reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]]));
            assert(filter_chars(reverse_seq(s), c) == filter_chars(reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]]), c));
            assert(filter_chars(reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]]), c) == 
                filter_chars(reverse_seq(s.subrange(1, s.len() as int)), c));
        } else {
            assert(filter_chars(s, c) == seq![s[0]].add(filter_chars(s.subrange(1, s.len() as int), c)));
            assert(reverse_seq(filter_chars(s, c)) == reverse_seq(seq![s[0]].add(filter_chars(s.subrange(1, s.len() as int), c))));
            assert(reverse_seq(seq![s[0]].add(filter_chars(s.subrange(1, s.len() as int), c))) == 
                reverse_seq(filter_chars(s.subrange(1, s.len() as int), c)).add(seq![s[0]]));
            assert(reverse_seq(s) == reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]]));
            assert(filter_chars(reverse_seq(s), c) == filter_chars(reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]]), c));
            assert(filter_chars(reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]]), c) == 
                seq![s[0]].add(filter_chars(reverse_seq(s.subrange(1, s.len() as int)), c)));
        }
    }
}

/* helper modified by LLM (iteration 5): Fixed invariants and assertions in filter_vec_chars */
fn filter_vec_chars(s: &Vec<char>, c: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@ == filter_chars(s@, c@),
        forall|i: int| #![auto] 0 <= i < result@.len() ==> !c@.contains(result@[i]),
        forall|i: int| #![auto] 0 <= i < result@.len() ==> s@.contains(result@[i]),
        result@.len() <= s@.len()
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result@ == filter_chars(s@.subrange(0, i as int), c@),
            forall|j: int| #![auto] 0 <= j < result@.len() ==> !c@.contains(result@[j]),
            forall|j: int| #![auto] 0 <= j < result@.len() ==> s@.contains(result@[j]),
            result@.len() <= i
        decreases s.len() - i
    {
        let current_char = s[i];
        let mut contains_char = false;
        let mut j: usize = 0;
        
        while j < c.len()
            invariant
                j <= c.len(),
                contains_char == (exists|k: int| 0 <= k < j as int && c@[k] == current_char)
            decreases c.len() - j
        {
            if c[j] == current_char {
                contains_char = true;
                break;
            }
            j += 1;
        }
        
        if !contains_char {
            result.push(current_char);
            proof {
                assert(forall|idx: int| #![auto] 0 <= idx < result@.len() ==> !c@.contains(result@[idx]));
                assert(forall|idx: int| #![auto] 0 <= idx < result@.len() ==> s@.contains(result@[idx]));
            }
        }
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 5): Fixed palindrome check with proper invariants */
fn is_palindrome(s: &Vec<char>) -> (result: bool)
    ensures
        result == (s@ == reverse_seq(s@))
{
    let mut left: usize = 0;
    let mut right: usize = s.len();
    
    while left < right
        invariant
            0 <= left <= right <= s.len(),
            s@.subrange(0, left as int) == reverse_seq(s@).subrange(s.len() as int - left as int, s.len() as int),
            s@.subrange(right as int, s.len() as int) == reverse_seq(s@).subrange(0, s.len() as int - right as int),
            s@.subrange(left as int, right as int) == reverse_seq(s@.subrange(left as int, right as int))
        decreases right - left
    {
        right -= 1;
        if s[left] != s[right] {
            return false;
        }
        left += 1;
    }
    true
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
    /* code modified by LLM (iteration 5): Fixed implementation with proper verification */
    let filtered = filter_vec_chars(&s, &c);
    let is_pal = is_palindrome(&filtered);
    proof {
        reverse_seq_filter_commute(filtered@, c@);
        assert(filtered@ == filter_chars(s@, c@));
        if is_pal {
            assert(filtered@ == reverse_seq(filtered@));
        } else {
            assert(filtered@ != reverse_seq(filtered@));
        }
    }
    (filtered, is_pal)
}
// </vc-code>


}

fn main() {}