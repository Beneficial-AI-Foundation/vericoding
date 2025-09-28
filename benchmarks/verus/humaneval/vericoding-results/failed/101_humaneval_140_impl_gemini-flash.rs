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
        exists|j: int| 0 <= j < result.len() && ( #[trigger] result[j] == '_' || #[trigger] result[j] == '-'))
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. */
fn is_space(c: char) -> bool {
    c == ' '
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
/* code modified by LLM (iteration 5): The previous fix was incorrect, it should have been `==>` for Verus implications. Corrected the forall loop syntax. */
{
    let mut result_vec: Vec<char> = Vec::new();

    if text.len() == 0 {
        return Seq::empty();
    }

    let mut i: int = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            forall|k: int| 0 <= k < result_vec.len() ==> !is_space(result_vec@[k]),
            forall|x: int, y: int| 0 <= x < y < i && !is_space(text@x) && !is_space(text@y)
                ==>
                exists|x_prime: int, y_prime: int| 0 <= x_prime < y_prime < result_vec.len() && result_vec@[x_prime] == text@x && result_vec@[y_prime] == text@y,
        decreases text.len() - i
    {
        if is_space(text@i) {
            if i == 0 || !is_space(text@(i - 1)) {
                result_vec.push('_');
            }
        } else {
            result_vec.push(text@i);
        }
        i = i + 1;
    }

    result_vec.view()
}
// </vc-code>


}

fn main() {}