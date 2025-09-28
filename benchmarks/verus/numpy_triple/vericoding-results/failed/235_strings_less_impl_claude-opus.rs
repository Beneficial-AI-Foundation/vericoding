// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn str_less_than(s1: String, s2: String) -> bool;

fn less(x1: &Vec<String>, x2: &Vec<String>) -> (result: Vec<bool>)
    requires x1@.len() == x2@.len(),
    ensures 
        result@.len() == x1@.len(),

        forall|i: int| 0 <= i < result@.len() ==> result@[i] == str_less_than(x1@[i], x2@[i]),

        forall|i: int| 0 <= i < result@.len() && result@[i] == true ==> !str_less_than(x2@[i], x1@[i]),

        forall|i: int| 0 <= i < result@.len() && x1@[i] == x2@[i] ==> result@[i] == false,

        forall|i: int| 0 <= i < result@.len() ==> result@[i] == true || result@[i] == false,

        forall|i: int| 0 <= i < result@.len() && result@[i] == true ==> x1@[i] != x2@[i],

        forall|i: int| 0 <= i < result@.len() ==> result@[i] == true || x1@[i] == x2@[i] || str_less_than(x2@[i], x1@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using explicit string comparison with character-by-character logic */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < x1.len()
        invariant
            i <= x1.len(),
            x1@.len() == x2@.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j] == str_less_than(x1@[j], x2@[j]),
            forall|j: int| 0 <= j < i && result@[j] == true ==> !str_less_than(x2@[j], x1@[j]),
            forall|j: int| 0 <= j < i && x1@[j] == x2@[j] ==> result@[j] == false,
            forall|j: int| 0 <= j < i ==> result@[j] == true || result@[j] == false,
            forall|j: int| 0 <= j < i && result@[j] == true ==> x1@[j] != x2@[j],
            forall|j: int| 0 <= j < i ==> result@[j] == true || x1@[j] == x2@[j] || str_less_than(x2@[j], x1@[j]),
    {
        let s1 = &x1[i];
        let s2 = &x2[i];
        
        // Compare strings lexicographically using character comparison
        let mut is_less = false;
        let mut j: usize = 0;
        let len1 = s1.unicode_len();
        let len2 = s2.unicode_len();
        let min_len = if len1 <= len2 { len1 } else { len2 };
        
        let mut found_diff = false;
        while j < min_len && !found_diff
        {
            let c1 = s1.get_char(j as int);
            let c2 = s2.get_char(j as int);
            if c1 < c2 {
                is_less = true;
                found_diff = true;
            } else if c1 > c2 {
                is_less = false;
                found_diff = true;
            }
            j = j + 1;
        }
        
        // If all compared characters are equal, shorter string is less
        if !found_diff {
            is_less = len1 < len2;
        }
        
        result.push(is_less);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}