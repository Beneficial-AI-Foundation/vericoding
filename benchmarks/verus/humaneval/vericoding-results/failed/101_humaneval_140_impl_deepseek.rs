// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(text: Seq<char>) -> bool {
    true
}

spec fn is_space_sequence(text: Seq<char>, start: int, end: int) -> bool {
    &&& 0 <= start <= end < text.len()
    &&& (forall|k: int| start <= k <= end ==> text[k] == ' ')
    &&& (start == 0 || text[start-1] != ' ')
    &&& (end == text.len()-1 || text[end+1] != ' ')
}

spec fn valid_result(text: Seq<char>, result: Seq<char>) -> bool {
    &&& result.len() <= text.len()
    &&& (text.len() == 0 ==> result.len() == 0)
    &&& (forall|i: int| 0 <= i < result.len() ==> result[i] != ' ')
    &&& (forall|i: int| 0 <= i < result.len() ==> result[i] == '_' || result[i] == '-' || text.contains(result[i]))
    &&& ((forall|i: int| 0 <= i < text.len() ==> text[i] != ' ') ==> result == text)
    &&& (forall|i: int| 0 <= i < text.len() && text[i] != ' ' ==> result.contains(text[i]))
}

spec fn preserves_order(text: Seq<char>, result: Seq<char>) -> bool {
    forall|i: int, j: int| 0 <= i < j < text.len() && text[i] != ' ' && text[j] != ' ' ==>
        exists|i_prime: int, j_prime: int| 0 <= i_prime < j_prime < result.len() && result[i_prime] == text[i] && result[j_prime] == text[j]
}

spec fn correct_space_transformation(text: Seq<char>, result: Seq<char>) -> bool {
    &&& (forall|i: int| 0 <= i < text.len() ==> #[trigger] text[i] != ' ' ==> result.contains(#[trigger] text[i]))
    &&& (forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] != ' ')
    &&& (forall|i: int, j: int| 0 <= i < j < text.len() && #[trigger] text[i] != ' ' && #[trigger] text[j] != ' ' ==>
        exists|i_prime: int, j_prime: int| 0 <= i_prime < j_prime < result.len() && result[i_prime] == #[trigger] text[i] && result[j_prime] == #[trigger] text[j])
    &&& (forall|i: int| 0 <= i < text.len() && #[trigger] text[i] == ' ' ==> 
        (i == 0 || text[i-1] != ' ') && (i == text.len()-1 || text[i+1] != ' ') ==> 
        exists|j: int| 0 <= j < result.len() && ( #[
            trigger] result[j] == '_' || #[trigger] result[j] == '-'))
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove problematic type conversion and add proof utilities */
fn int_to_usize(i: int) -> (u: usize)
    requires
        0 <= i,
    ensures
        u == i as usize
{
    i as usize
}
// </vc-helpers>

// <vc-spec>
fn fix_spaces(text: Seq<char>) -> (result: Seq<char>)
    requires 
        valid_input(text),
    ensures 
        valid_result(text, result),
        preserves_order(text, result),
        correct_space_transformation(text, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix ghost type usage and improve verification */
{
    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    let text_len = text.len() as int;
    
    while i < (text_len as usize)
        invariant
            0 <= (i as int) <= text_len,
            forall|k: int| 0 <= k < result_vec.len() as int ==> result_vec@[k] != ' ',
            forall|k: int| 0 <= k < text_len && text[k] != ' ' ==> (exists|l: int| 0 <= l < result_vec.len() as int && result_vec@[l] == text[k]),
            forall|k: int, l: int| 0 <= k < l < text_len && text[k] != ' ' && text[l] != ' ' ==> 
                (exists|k_prime: int, l_prime: int| 0 <= k_prime < l_prime < result_vec.len() as int && result_vec@[k_prime] == text[k] && result_vec@[l_prime] == text[l])
    {
        let i_int = i as int;
        if text[i_int] != ' ' {
            result_vec.push(text[i_int]);
            i = i + 1;
        } else {
            let mut j = i;
            while j < (text_len as usize) && text[j as int] == ' '
                invariant
                    (i as int) <= (j as int) <= text_len,
                    forall|k: int| (i as int) <= k < (j as int) ==> text[k] == ' ',
                    (i == 0 || text[(i as int) - 1] != ' '), 
                    j < (text_len as usize) ==> text[j as int] != ' '
            {
                j = j + 1;
            }
            
            if i > 0 && j < (text_len as usize) {
                result_vec.push('-');
            }
            
            i = j;
        }
    }
    
    let result = result_vec.into_seq();
    result
}
// </vc-code>


}

fn main() {}