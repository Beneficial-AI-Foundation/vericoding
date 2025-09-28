// <vc-preamble>
use vstd::prelude::*;

verus! {

enum SplitResult {
    StringSeq { words: Seq<Seq<char>> },
    Count { value: int },
}

spec fn contains_space(txt: Seq<char>) -> bool {
    exists|i: int| 0 <= i < txt.len() && txt[i] == ' '
}

spec fn contains_comma(txt: Seq<char>) -> bool {
    exists|i: int| 0 <= i < txt.len() && txt[i] == ','
}
// </vc-preamble>

// <vc-helpers>
spec fn split_on_whitespace(txt: Seq<char>) -> Seq<Seq<char>>
    decreases txt.len()
{
    if txt.len() == 0 {
        seq![]
    } else {
        split_on_whitespace_helper(txt, 0, seq![], seq![])
    }
}

/* helper modified by LLM (iteration 5): fixed type compatibility for nat comparisons */
spec fn split_on_whitespace_helper(txt: Seq<char>, i: int, result: Seq<Seq<char>>, current_word: Seq<char>) -> Seq<Seq<char>>
    decreases txt.len() - i
{
    if i >= txt.len() as int {
        if current_word.len() > 0 {
            result.push(current_word)
        } else {
            result
        }
    } else if txt@[i] == ' ' {
        if current_word.len() > 0 {
            split_on_whitespace_helper(txt, i + 1, result.push(current_word), seq![])
        } else {
            split_on_whitespace_helper(txt, i + 1, result, seq![])
        }
    } else {
        split_on_whitespace_helper(txt, i + 1, result, current_word.push(txt@[i]))
    }
}

spec fn split_on_comma(txt: Seq<char>) -> Seq<Seq<char>>
    decreases txt.len()
{
    if txt.len() == 0 {
        seq![seq![]]
    } else {
        split_on_comma_helper(txt, 0, seq![], seq![])
    }
}

/* helper modified by LLM (iteration 5): fixed type compatibility for nat comparisons */
spec fn split_on_comma_helper(txt: Seq<char>, i: int, result: Seq<Seq<char>>, current_word: Seq<char>) -> Seq<Seq<char>>
    decreases txt.len() - i
{
    if i >= txt.len() as int {
        result.push(current_word)
    } else if txt@[i] == ',' {
        split_on_comma_helper(txt, i + 1, result.push(current_word), seq![])
    } else {
        split_on_comma_helper(txt, i + 1, result, current_word.push(txt@[i]))
    }
}

spec fn count_odd_position_lowercase(txt: Seq<char>) -> int {
    count_odd_position_lowercase_helper(txt, 0)
}

/* helper modified by LLM (iteration 5): fixed type compatibility for nat comparisons */
spec fn count_odd_position_lowercase_helper(txt: Seq<char>, i: int) -> int
    decreases txt.len() - i
{
    if i >= txt.len() as int {
        0
    } else {
        let c = txt@[i];
        let count_rest = count_odd_position_lowercase_helper(txt, i + 1);
        if 'a' <= c <= 'z' && (c as int - 'a' as int) % 2 == 1 {
            1 + count_rest
        } else {
            count_rest
        }
    }
}

/* helper modified by LLM (iteration 5): fixed type compatibility for nat comparisons */
exec fn contains_space_exec(txt: Seq<char>) -> bool {
    let mut i = 0;
    while i < txt.len() as int
        invariant 0 <= i <= txt.len() as int
        decreases (txt.len() as int) - i
    {
        if txt@[i] == ' ' {
            return true;
        }
        i += 1;
    }
    false
}

/* helper modified by LLM (iteration 5): fixed type compatibility for nat comparisons */
exec fn contains_comma_exec(txt: Seq<char>) -> bool {
    let mut i = 0;
    while i < txt.len() as int
        invariant 0 <= i <= txt.len() as int
        decreases (txt.len() as int) - i
    {
        if txt@[i] == ',' {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn split_words(txt: Vec<char>) -> (result: SplitResult)
    ensures 
        (contains_space(txt@) ==> matches!(result, SplitResult::StringSeq { .. })) &&
        (!contains_space(txt@) && contains_comma(txt@) ==> matches!(result, SplitResult::StringSeq { .. })) &&
        (!contains_space(txt@) && !contains_comma(txt@) ==> matches!(result, SplitResult::Count { .. })) &&
        (contains_space(txt@) ==> result == SplitResult::StringSeq { words: split_on_whitespace(txt@) }) &&
        (!contains_space(txt@) && contains_comma(txt@) ==> 
            result == SplitResult::StringSeq { words: split_on_comma(txt@) }) &&
        (!contains_space(txt@) && !contains_comma(txt@) ==> 
            result == SplitResult::Count { value: count_odd_position_lowercase(txt@) }) &&
        (match result {
            SplitResult::StringSeq { words } => words.len() >= 0,
            SplitResult::Count { value } => value >= 0,
        }) &&
        (contains_space(txt@) ==> match result {
            SplitResult::StringSeq { words } => forall|w: Seq<char>| words.contains(w) ==> w.len() > 0,
            _ => true,
        }) &&
        (!contains_space(txt@) && contains_comma(txt@) ==> match result {
            SplitResult::StringSeq { words } => words.len() > 0,
            _ => true,
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using corrected exec functions with proper type casting */
    if contains_space_exec(txt@) {
        let words = split_on_whitespace(txt@);
        SplitResult::StringSeq { words }
    } else if contains_comma_exec(txt@) {
        let words = split_on_comma(txt@);
        SplitResult::StringSeq { words }
    } else {
        let value = count_odd_position_lowercase(txt@);
        SplitResult::Count { value }
    }
}
// </vc-code>


}

fn main() {}