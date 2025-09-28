// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

spec fn all_chars_alpha(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alpha_char(s[0]) && all_chars_alpha(s.skip(1))
    }
}

fn isalpha(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i as int] == (a[i as int]@.len() > 0 && all_chars_alpha(a[i as int]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() == 0 ==> result[i as int] == false),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() > 0 ==> (result[i as int] <==> all_chars_alpha(a[i as int]@))),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> a[i as int]@.len() > 0),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> all_chars_alpha(a[i as int]@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type mismatches in invariant from usize to int */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as int] == (a[j as int]@.len() > 0 && all_chars_alpha(a[j as int]@))
    {
        let s = a[i as usize].clone();
        let mut current_is_alpha = true;
        
        if s.len() == 0 {
            current_is_alpha = false;
        } else {
            let mut k: usize = 0;
            while k < s.len()
                invariant
                    0 <= k && k <= s.len(),
                    current_is_alpha == 
                        (forall|l: int|
                            0 <= l && l < k ==> is_alpha_char(s@[l as int])),
                    // Added forall condition here based on previous iteration's proof block
                    forall|l: int| 0 <= l < k ==> is_alpha_char(s@[l as int]) || !current_is_alpha
            {
                if !is_alpha_char(s.as_str().chars().nth(k as usize).unwrap()) {
                    current_is_alpha = false;
                    break;
                }
                k = k + 1;
            }
            proof {
                if current_is_alpha {
                    assert(forall|l: int| 0 <= l < s.len() ==> is_alpha_char(s@[l as int]));
                    assert(all_chars_alpha(s@));
                } else {
                    assert(exists|l: int| 0 <= l < s.len() && !is_alpha_char(s@[l as int]));
                    assert(!all_chars_alpha(s@));
                }
                assert(current_is_alpha == all_chars_alpha(s@));
            }
        }
        
        result.push(current_is_alpha);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}