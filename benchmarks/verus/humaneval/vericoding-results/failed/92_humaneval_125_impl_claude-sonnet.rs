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
/* helper modified by LLM (iteration 5): fixed char arithmetic to use proper casting to u32 */
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
        if 'a' <= c <= 'z' && (c as u32 - 'a' as u32) % 2 == 1 {
            1 + count_rest
        } else {
            count_rest
        }
    }
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
/* code modified by LLM (iteration 5): fixed int casting issue by using as int instead of int() */
{
    let mut has_space = false;
    let mut has_comma = false;
    
    let mut i = 0;
    while i < txt.len()
        invariant
            0 <= i <= txt.len(),
            has_space ==> contains_space(txt@),
            has_comma ==> contains_comma(txt@),
            !has_space ==> forall|j: int| 0 <= j < i ==> txt@[j] != ' ',
            !has_comma ==> forall|j: int| 0 <= j < i ==> txt@[j] != ','
    {
        if txt[i] == ' ' {
            has_space = true;
        }
        if txt[i] == ',' {
            has_comma = true;
        }
        i += 1;
    }
    
    if has_space {
        let words = split_on_whitespace_exec(txt);
        let words_seq = seq_from_vec(words);
        SplitResult::StringSeq { words: words_seq }
    } else if has_comma {
        let words = split_on_comma_exec(txt);
        let words_seq = seq_from_vec(words);
        SplitResult::StringSeq { words: words_seq }
    } else {
        let count = count_odd_position_lowercase_exec(txt);
        SplitResult::Count { value: count as int }
    }
}

fn seq_from_vec(v: Vec<Vec<char>>) -> (result: Seq<Seq<char>>)
    ensures result.len() == v@.len()
{
    let mut result = seq![];
    let mut i = 0;
    while i < v.len()
        invariant 
            0 <= i <= v.len(),
            result.len() == i
    {
        result = result.push(v[i]@);
        i += 1;
    }
    result
}

fn split_on_whitespace_exec(txt: Vec<char>) -> (result: Vec<Vec<char>>)
    ensures result@.len() >= 0
{
    let mut result = Vec::new();
    let mut current_word = Vec::new();
    
    let mut i = 0;
    while i < txt.len()
        invariant 0 <= i <= txt.len()
    {
        if txt[i] == ' ' {
            if current_word.len() > 0 {
                result.push(current_word);
                current_word = Vec::new();
            }
        } else {
            current_word.push(txt[i]);
        }
        i += 1;
    }
    
    if current_word.len() > 0 {
        result.push(current_word);
    }
    
    result
}

fn split_on_comma_exec(txt: Vec<char>) -> (result: Vec<Vec<char>>)
    ensures result@.len() > 0
{
    let mut result = Vec::new();
    let mut current_word = Vec::new();
    
    if txt.len() == 0 {
        result.push(Vec::new());
        return result;
    }
    
    let mut i = 0;
    while i < txt.len()
        invariant 0 <= i <= txt.len()
    {
        if txt[i] == ',' {
            result.push(current_word);
            current_word = Vec::new();
        } else {
            current_word.push(txt[i]);
        }
        i += 1;
    }
    
    result.push(current_word);
    result
}

fn count_odd_position_lowercase_exec(txt: Vec<char>) -> (result: u32)
    ensures result >= 0
{
    let mut count = 0u32;
    let mut i = 0;
    
    while i < txt.len()
        invariant
            0 <= i <= txt.len(),
            count >= 0
    {
        let c = txt[i];
        if 'a' <= c && c <= 'z' && (c as u32 - 'a' as u32) % 2 == 1 {
            count += 1;
        }
        i += 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}