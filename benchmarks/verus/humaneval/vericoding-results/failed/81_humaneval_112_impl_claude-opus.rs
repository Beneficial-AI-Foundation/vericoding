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
/* helper modified by LLM (iteration 5): Fixed syntax for helper functions */
proof fn filter_chars_properties(s: Seq<char>, c: Seq<char>)
    ensures
        filter_chars(s, c).len() <= s.len(),
        forall|i: int| 0 <= i < filter_chars(s, c).len() ==> !c.contains(filter_chars(s, c)[i]),
        forall|i: int| 0 <= i < filter_chars(s, c).len() ==> s.contains(filter_chars(s, c)[i]),
    decreases s.len()
{
    if s.len() == 0 {
    } else if c.contains(s[0]) {
        filter_chars_properties(s.subrange(1, s.len() as int), c);
    } else {
        filter_chars_properties(s.subrange(1, s.len() as int), c);
        let rest = filter_chars(s.subrange(1, s.len() as int), c);
        assert(forall|i: int| 0 <= i < rest.len() ==> s.subrange(1, s.len() as int).contains(rest[i]));
        assert(s.contains(s[0]));
        assert(forall|i: int| 1 <= i < filter_chars(s, c).len() ==> filter_chars(s, c)[i] == rest[i - 1]);
        assert(forall|i: int| 1 <= i < filter_chars(s, c).len() ==> s.contains(filter_chars(s, c)[i]));
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
    /* code modified by LLM (iteration 5): Fixed trigger syntax by using proper closure syntax */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@ == filter_chars(s@.subrange(0, i as int), c@),
            result@.len() <= i,
            forall|j: int| 0 <= j < result@.len() ==> !c@.contains(result@[j]),
            forall|j: int| 0 <= j < result@.len() ==> s@.subrange(0, i as int).contains(result@[j]),
        decreases s.len() - i
    {
        let ch = s[i];
        let mut found = false;
        let mut j = 0;
        
        while j < c.len()
            invariant
                0 <= j <= c.len(),
                found == c@.subrange(0, j as int).contains(ch),
            decreases c.len() - j
        {
            if c[j] == ch {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if !found {
            result.push(ch);
        }
        
        assert(filter_chars(s@.subrange(0, (i + 1) as int), c@) == 
               if c@.contains(s@[i as int]) {
                   filter_chars(s@.subrange(0, i as int), c@)
               } else {
                   filter_chars(s@.subrange(0, i as int), c@).push(s@[i as int])
               });
        
        i = i + 1;
    }
    
    assert(s@.subrange(0, s.len() as int) == s@);
    proof {
        filter_chars_properties(s@, c@);
    }
    
    let mut is_palindrome = true;
    let mut k = 0;
    
    while k < result.len() / 2
        invariant
            0 <= k <= result.len() / 2,
            is_palindrome == forall|j: int| 0 <= j < k ==> result@[j] == result@[result@.len() - 1 - j],
        decreases result.len() / 2 - k
    {
        if result[k] != result[result.len() - 1 - k] {
            is_palindrome = false;
            break;
        }
        k = k + 1;
    }
    
    (result, is_palindrome)
}
// </vc-code>


}

fn main() {}