// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed ensures from spec fn to fix compilation error */
spec fn is_string_decimal(s: Seq<char>) -> bool {
    s.len() > 0 && all_chars_decimal(s)
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
/* code modified by LLM (iteration 5): fixed index type to usize with ghost variable for decreases */
{
    let mut result: Vec<bool> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    proof {
        let mut ghost_i: int = 0;
    }
    while i < a.len()
        invariant
            ghost_i == i as int,
            0 <= ghost_i <= a.len() as int,
            result.len() as int == ghost_i,
            forall|j: int| 0 <= j < ghost_i ==> result[j as usize] == is_string_decimal(a[j as usize]@)
        decreases a.len() as int - ghost_i
    {
        let b = is_string_decimal(a[i]@);
        result.push(b);
        i = i + 1;
        proof { ghost_i = ghost_i + 1; }
    }
    result
}
// </vc-code>


}
fn main() {}