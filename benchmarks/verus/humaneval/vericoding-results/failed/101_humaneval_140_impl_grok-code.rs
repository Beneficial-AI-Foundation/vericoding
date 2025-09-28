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
spec fn is_single_space(text: Seq<char>, i: int) -> bool {
    &&& 0 <= i < text.len()
    &&& text[i] == ' '
    &&& (i == 0 || text[i-1] != ' ')
    &&& (i == text.len()-1 || text[i+1] != ' ')
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
{
    /* code modified by LLM (iteration 3): Fixed type mismatches, corrected invariant condition */
    let mut result = Seq::empty();
    let mut i = 0nat;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() ==> result[k] == '_' || text.contains(result[k]),
    {
        if text.index(i as int) != ' ' {
            result = result.push(text.index(i as int));
        } else if is_single_space(text, i as int) {
            result = result.push('_');
        }
        i = i + 1nat;
    }
    result
}
// </vc-code>


}

fn main() {}