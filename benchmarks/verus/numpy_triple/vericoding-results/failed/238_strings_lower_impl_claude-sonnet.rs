// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing 'lemma' keyword and using proper function declaration */
fn string_to_lower_len(s: Seq<char>)
    ensures string_to_lower(s).len() == s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        string_to_lower_len(s.skip(1));
    }
}

fn string_to_lower_idempotent(s: Seq<char>)
    ensures string_to_lower(string_to_lower(s)) == string_to_lower(s)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        string_to_lower_idempotent(s.skip(1));
    }
}

fn char_to_lower_impl(c: char) -> (result: char)
    ensures result == char_to_lower(c)
{
    if c >= 'A' && c <= 'Z' {
        ((c as u8 - 'A' as u8) + 'a' as u8) as char
    } else {
        c
    }
}

fn string_to_lower_impl(s: Vec<char>) -> (result: Vec<char>)
    ensures
        result@ == string_to_lower(s@),
        result.len() == s.len()
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            result@ == string_to_lower(s@.take(i as int))
    {
        let lower_char = char_to_lower_impl(s[i]);
        result.push(lower_char);
        i += 1;
    }
    proof {
        assert(s@.take(s.len() as int) == s@);
    }
    result
}
// </vc-helpers>

// <vc-spec>
spec fn char_to_lower(c: char) -> char;

spec fn string_to_lower(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        seq![char_to_lower(s[0])] + string_to_lower(s.skip(1))
    }
}

fn lower(a: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@ == string_to_lower(a[i]@),
        forall|i: int| 0 <= i < a.len() ==> result[i].len() == a[i].len(),
        forall|i: int| 0 <= i < a.len() ==> (a[i].len() == 0 ==> result[i].len() == 0),
        forall|i: int| 0 <= i < a.len() ==> string_to_lower(result[i]@) == result[i]@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added closing brace to complete function signature */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j]@ == string_to_lower(a[j]@),
            forall|j: int| 0 <= j < i ==> result[j].len() == a[j].len(),
            forall|j: int| 0 <= j < i ==> string_to_lower(result[j]@) == result[j]@
    {
        let lower_string = string_to_lower_impl(a[i]);
        
        proof {
            string_to_lower_len(a[i]@);
            string_to_lower_idempotent(a[i]@);
        }
        
        result.push(lower_string);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}