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
spec fn count_non_spaces(text: Seq<char>) -> nat {
    text.filter(|c: char| c != ' ').len()
}

spec fn is_single_space(text: Seq<char>, i: int) -> bool {
    &&& 0 <= i < text.len()
    &&& text[i] == ' '
    &&& (i == 0 || text[i-1] != ' ')
    &&& (i == text.len()-1 || text[i+1] != ' ')
}

/* helper modified by LLM (iteration 5): fixed return type and arithmetic */
spec fn count_single_spaces(text: Seq<char>) -> nat {
    if text.len() >= count_non_spaces(text) {
        (text.len() - count_non_spaces(text)) as nat
    } else {
        0nat
    }
}

proof fn lemma_result_length(text: Seq<char>)
    ensures count_non_spaces(text) + count_single_spaces(text) <= text.len()
{
}

proof fn lemma_empty_text()
    ensures valid_result(Seq::<char>::empty(), Seq::<char>::empty())
{
}

proof fn lemma_no_spaces_preserved(text: Seq<char>)
    requires forall|i: int| 0 <= i < text.len() ==> text[i] != ' '
    ensures
        valid_result(text, text),
        preserves_order(text, text),
        correct_space_transformation(text, text)
{
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
    /* code modified by LLM (iteration 5): removed int casts in executable code */
    if text.len() == 0nat {
        proof { lemma_empty_text(); }
        return Seq::<char>::empty();
    }
    
    let mut result = Vec::<char>::new();
    let mut i: usize = 0;
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            forall|j: int| 0 <= j < result.len() ==> result@[j] != ' ',
            forall|j: int| 0 <= j < i && text[j] != ' ' ==> result@.contains(text[j]),
            forall|j: int| 0 <= j < result.len() ==> result@[j] == '_' || result@[j] == '-' || text.contains(result@[j])
    {
        if text[i] != ' ' {
            result.push(text[i]);
        } else {
            let is_single = (i == 0 || text[i-1] != ' ') && (i == text.len()-1 || text[i+1] != ' ');
            if is_single {
                if i % 2 == 0 {
                    result.push('_');
                } else {
                    result.push('-');
                }
            }
        }
        i = i + 1;
    }
    
    result@
}
// </vc-code>


}

fn main() {}