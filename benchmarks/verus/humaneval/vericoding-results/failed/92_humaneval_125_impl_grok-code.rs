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

spec fn split_on_whitespace_helper(txt: Seq<char>, i: int, result: Seq<Seq<char>>, current_word: Seq<char>) -> Seq<Seq<char>>
    decreases txt.len() - i when 0 <= i <= txt.len()
{
    if i >= txt.len() {
        if current_word.len() > 0 {
            result.push(current_word)
        } else {
            result
        }
    } else if txt[i] == ' ' {
        if current_word.len() > 0 {
            split_on_whitespace_helper(txt, i + 1, result.push(current_word), seq![])
        } else {
            split_on_whitespace_helper(txt, i + 1, result, seq![])
        }
    } else {
        split_on_whitespace_helper(txt, i + 1, result, current_word.push(txt[i]))
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

spec fn split_on_comma_helper(txt: Seq<char>, i: int, result: Seq<Seq<char>>, current_word: Seq<char>) -> Seq<Seq<char>>
    decreases txt.len() - i when 0 <= i <= txt.len()
{
    if i >= txt.len() {
        result.push(current_word)
    } else if txt[i] == ',' {
        split_on_comma_helper(txt, i + 1, result.push(current_word), seq![])
    } else {
        split_on_comma_helper(txt, i + 1, result, current_word.push(txt[i]))
    }
}

spec fn count_odd_position_lowercase(txt: Seq<char>) -> int {
    count_odd_position_lowercase_helper(txt, 0)
}

spec fn count_odd_position_lowercase_helper(txt: Seq<char>, i: int) -> int
    decreases txt.len() - i when 0 <= i <= txt.len()
{
    if i >= txt.len() {
        0
    } else {
        let c = txt[i];
        let count_rest = count_odd_position_lowercase_helper(txt, i + 1);
        if 'a' <= c <= 'z' && (c as int - 'a' as int) % 2 == 1 {
            1 + count_rest
        } else {
            count_rest
        }
    }
}

/* helper modified by LLM (iteration 5): fixed contains_space_exec to use Vec indexing without int type */
fn contains_space_exec(txt: &Vec<char>) -> (result: bool)
    ensures result == contains_space(txt@)
{
    for i in 0..txt.len() {
        if txt[i] == ' ' {
            return true;
        }
    }
    false
}

/* helper modified by LLM (iteration 5): fixed contains_comma_exec to use Vec indexing without int type */
fn contains_comma_exec(txt: &Vec<char>) -> (result: bool)
    ensures result == contains_comma(txt@)
{
    for i in 0..txt.len() {
        if txt[i] == ',' {
            return true;
        }
    }
    false
}

/* helper modified by LLM (iteration 5): fixed split_on_whitespace_exec to use Vec indexing and usize without int */
fn split_on_whitespace_exec(txt: &Vec<char>) -> (result: Vec<Vec<char>>)
    ensures result@ == split_on_whitespace(txt@)
{
    let mut result = Vec::<Vec<char>>::new();
    let mut current_word = Vec::<char>::new();
    for i in 0..txt.len() {
        let c = txt[i];
        if c == ' ' {
            if !current_word.is_empty() {
                result.push(current_word);
                current_word = Vec::<char>::new();
            }
        } else {
            current_word.push(c);
        }
    }
    if !current_word.is_empty() {
        result.push(current_word);
    }
    result
}

/* helper modified by LLM (iteration 5): fixed split_on_comma_exec to use Vec indexing and usize without int */
fn split_on_comma_exec(txt: &Vec<char>) -> (result: Vec<Vec<char>>)
    ensures result@ == split_on_comma(txt@)
{
    let mut result = Vec::<Vec<char>>::new();
    let mut current_word = Vec::<char>::new();
    for i in 0..txt.len() {
        let c = txt[i];
        if c == ',' {
            result.push(current_word);
            current_word = Vec::<char>::new();
        } else {
            current_word.push(c);
        }
    }
    result.push(current_word);
    result
}

/* helper modified by LLM (iteration 5): fixed count_odd_position_lowercase_exec to use u32 arithmetic without int */
fn count_odd_position_lowercase_exec(txt: &Vec<char>) -> (result: i64)
    ensures result as int == count_odd_position_lowercase(txt@)
{
    let mut count = 0i64;
    for i in 0..txt.len() {
        let c = txt[i];
        if 'a' <= c && c <= 'z' {
            let idx = (c as u32 - 'a' as u32) % 2;
            if idx == 1 {
                count += 1;
            }
        }
    }
    count
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
/* code modified by LLM (iteration 5): no changes, main logic calls the fixed exec helpers */
{
    if contains_space_exec(&txt) {
        SplitResult::StringSeq { words: split_on_whitespace_exec(&txt).view() }
    } else if contains_comma_exec(&txt) {
        SplitResult::StringSeq { words: split_on_comma_exec(&txt).view() }
    } else {
        SplitResult::Count { value: count_odd_position_lowercase_exec(&txt) }
    }
}
// </vc-code>


}

fn main() {}