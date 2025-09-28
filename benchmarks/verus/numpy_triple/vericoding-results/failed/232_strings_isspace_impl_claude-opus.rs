// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed string handling to work with vstd string specifications */
spec fn all_chars_whitespace_rec(s: Seq<char>, start: int) -> bool
    decreases s.len() - start when 0 <= start <= s.len()
{
    if start >= s.len() {
        true
    } else if start < 0 {
        false
    } else {
        is_whitespace_char(s[start]) && all_chars_whitespace_rec(s, start + 1)
    }
}

proof fn lemma_all_chars_whitespace_equiv(s: Seq<char>)
    ensures
        all_chars_whitespace(s) == all_chars_whitespace_rec(s, 0),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_all_chars_whitespace_equiv(s.skip(1));
        assert(s.skip(1) =~= s.subrange(1, s.len() as int));
    }
}

fn check_all_whitespace_str(s: &String) -> (result: bool)
    ensures
        result == (s@.len() > 0 && all_chars_whitespace(s@)),
{
    if s.unicode_len() == 0 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < s.unicode_len()
        invariant
            0 <= i <= s.unicode_len(),
            s@.len() == s.unicode_len() as int,
            all_chars_whitespace_rec(s@, i as int),
    {
        let c = s.get_char(i);
        if !(c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c') {
            proof {
                lemma_all_chars_whitespace_equiv(s@);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        lemma_all_chars_whitespace_equiv(s@);
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn is_whitespace_char(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
}

spec fn all_chars_whitespace(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_whitespace_char(s[0]) && all_chars_whitespace(s.skip(1))
    }
}

fn isspace(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_whitespace(a[i]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i]@.len() == 0 ==> result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Pass String reference directly without deref */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@)),
            forall|j: int| 0 <= j < i ==> 
                (a[j]@.len() == 0 ==> result[j] == false),
    {
        let is_all_whitespace = check_all_whitespace_str(&a[i]);
        result.push(is_all_whitespace);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}