// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by adding empty parentheses */
spec fn is_empty_string(s: Seq<char>) -> bool {
    s.len() == 0
}

fn lemma all_chars_decimal_empty()
    ensures all_chars_decimal(Seq::<char>::empty())
{
}

fn lemma all_chars_decimal_single(c: char)
    ensures all_chars_decimal(seq![c]) == is_decimal_char(c)
{
}

fn check_all_chars_decimal(s: &str) -> (result: bool)
    ensures result == all_chars_decimal(s@)
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            all_chars_decimal(s@.take(i as int)),
    {
        let c = s.get_char(i);
        if !('0' <= c && c <= '9') {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn is_decimal_char(c: char) -> bool {
    ('0' <= c && c <= '9')
}

spec fn all_chars_decimal(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_decimal_char(s[0]) && all_chars_decimal(s.skip(1))
    }
}

fn isdecimal(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (result[i] == true <==> (a[i]@.len() > 0 && all_chars_decimal(a[i]@)))
            &&& (a[i]@ == Seq::<char>::empty() ==> result[i] == false)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementation unchanged from previous iteration */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (result[j] == true <==> (a[j]@.len() > 0 && all_chars_decimal(a[j]@)))
                &&& (a[j]@ == Seq::<char>::empty() ==> result[j] == false)
            },
    {
        let s = &a[i];
        let is_valid = if s.len() == 0 {
            false
        } else {
            check_all_chars_decimal(s)
        };
        result.push(is_valid);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}