// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_chars_decimal_recursive(s: Seq<char>, idx: int) -> bool
    decreases s.len() - idx
{
    if idx >= s.len() {
        true
    } else {
        is_decimal_char(s[idx]) && all_chars_decimal_recursive(s, idx + 1)
    }
}

proof fn lemma_all_chars_decimal_equiv(s: Seq<char>)
    ensures
        all_chars_decimal(s) == all_chars_decimal_recursive(s, 0)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_all_chars_decimal_equiv(s.skip(1));
        assert(s.skip(1) =~= s.subrange(1, s.len() as int));
    }
}

/* helper modified by LLM (iteration 5): Fixed indexing to use usize instead of int for exec code */
fn check_all_decimal(s: &Seq<char>) -> (result: bool)
    ensures
        result == all_chars_decimal(s)
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            all_chars_decimal_recursive(s, i as int)
    {
        let c = s[i];
        if !(c >= '0' && c <= '9') {
            proof {
                lemma_all_chars_decimal_equiv(s);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        lemma_all_chars_decimal_equiv(s);
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
    /* code modified by LLM (iteration 5): Use s@ to access character sequence */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (result[j] == true <==> (a[j]@.len() > 0 && all_chars_decimal(a[j]@)))
                &&& (a[j]@ == Seq::<char>::empty() ==> result[j] == false)
            }
    {
        let s = &a[i];
        if s@.len() == 0 {
            result.push(false);
        } else {
            let is_dec = check_all_decimal(&s@);
            result.push(is_dec);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}