use vstd::prelude::*;

verus! {

spec fn inner_expr_replace_blanks_with_chars(str1: &Vec<char>, ch: char, i: int) -> (result: char) {
    if str1[i] == 32 {
        ch
    } else {
        str1[i]
    }
}
// pure-end

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace_blanks_with_chars(str1: &Vec<char>, ch: char) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == inner_expr_replace_blanks_with_chars(str1, ch, i),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < str1.len()
        invariant
            i <= str1.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == inner_expr_replace_blanks_with_chars(str1, ch, j),
        decreases str1.len() - i
    {
        let current_char = if str1[i] == ' ' {
            ch
        } else {
            str1[i]
        };
        
        result.push(current_char);
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}