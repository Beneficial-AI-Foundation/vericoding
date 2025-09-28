// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implement string comparison without unsupported chars().collect() */
fn compare_strings(s1: &String, s2: &String) -> (result: bool)
    ensures result == string_lex_ge(s1@, s2@)
{
    let len1 = s1.unicode_len();
    let len2 = s2.unicode_len();
    let min_len = if len1 < len2 { len1 } else { len2 };
    
    let mut i: usize = 0;
    
    while i < min_len
        invariant
            i <= min_len,
            min_len <= len1,
            min_len <= len2,
            min_len == if len1 < len2 { len1 } else { len2 },
            forall|j: int| 0 <= j < i ==> s1@[j] == s2@[j],
    {
        let c1 = s1.get_char(i);
        let c2 = s2.get_char(i);
        
        if c1 < c2 {
            return false;
        } else if c1 > c2 {
            return true;
        }
        i = i + 1;
    }
    
    // If all compared characters are equal, s1 >= s2 if s1 is at least as long as s2
    return len1 >= len2;
}
// </vc-helpers>

// <vc-spec>
spec fn string_lex_ge(s1: Seq<char>, s2: Seq<char>) -> bool
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 {
        true
    } else if s2.len() == 0 {
        true
    } else if s1[0] == s2[0] {
        string_lex_ge(s1.skip(1), s2.skip(1))
    } else {
        s1[0] >= s2[0]
    }
}

fn greater_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == string_lex_ge(x1[i]@, x2[i]@),
        /* Reflexive property: every string is >= itself */
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == true,
        /* Empty string properties */
        forall|i: int| 0 <= i < result.len() && x1[i]@ == Seq::<char>::empty() && x2[i]@ == Seq::<char>::empty() ==> result[i] == true,
        forall|i: int| 0 <= i < result.len() && x1[i]@ != Seq::<char>::empty() && x2[i]@ == Seq::<char>::empty() ==> result[i] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use helper function for string comparison */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_lex_ge(x1[j]@, x2[j]@),
    {
        let is_ge = compare_strings(&x1[i], &x2[i]);
        result.push(is_ge);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}