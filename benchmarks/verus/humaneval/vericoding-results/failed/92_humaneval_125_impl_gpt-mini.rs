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

/* helper modified by LLM (iteration 3): executable check for space in a Vec<char> */
fn contains_space_exec(txt: &Vec<char>) -> bool {
    let mut i: usize = 0;
    while i < txt.len()
        invariant
            i <= txt.len(),
        decreases txt.len() - i
    {
        if txt[i] == ' ' {
            return true;
        }
        i += 1;
    }
    false
}

/* helper modified by LLM (iteration 3): executable check for comma in a Vec<char> */
fn contains_comma_exec(txt: &Vec<char>) -> bool {
    let mut i: usize = 0;
    while i < txt.len()
        invariant
            i <= txt.len(),
        decreases txt.len() - i
    {
        if txt[i] == ',' {
            return true;
        }
        i += 1;
    }
    false
}

/* helper modified by LLM (iteration 3): executable split on whitespace for Vec<char> */
fn split_on_whitespace_exec(txt: &Vec<char>) -> Seq<Seq<char>> {
    let mut result: Seq<Seq<char>> = seq![];
    let mut current: Seq<char> = seq![];
    let mut i: usize = 0;
    while i < txt.len()
        invariant
            i <= txt.len(),
        decreases txt.len() - i
    {
        if txt[i] == ' ' {
            if current.len() > 0 {
                result = result.push(current);
                current = seq![];
            }
        } else {
            current = current.push(txt[i]);
        }
        i += 1;
    }
    if current.len() > 0 {
        result = result.push(current);
    }
    result
}

/* helper modified by LLM (iteration 3): executable split on comma for Vec<char> */
fn split_on_comma_exec(txt: &Vec<char>) -> Seq<Seq<char>> {
    if txt.len() == 0 {
        return seq![seq![]];
    }
    let mut result: Seq<Seq<char>> = seq![];
    let mut current: Seq<char> = seq![];
    let mut i: usize = 0;
    while i < txt.len()
        invariant
            i <= txt.len(),
        decreases txt.len() - i
    {
        if txt[i] == ',' {
            result = result.push(current);
            current = seq![];
        } else {
            current = current.push(txt[i]);
        }
        i += 1;
    }
    result = result.push(current);
    result
}

/* helper modified by LLM (iteration 3): executable count of lowercase letters with odd alphabet index */
fn count_odd_position_lowercase_exec(txt: &Vec<char>) -> usize {
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < txt.len()
        invariant
            i <= txt.len(),
        decreases txt.len() - i
    {
        let c = txt[i];
        if 'a' <= c && c <= 'z' {
            let diff = (c as usize) - ('a' as usize);
            if diff % 2 == 1 {
                cnt += 1;
            }
        }
        i += 1;
    }
    cnt
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
    /* code modified by LLM (iteration 3): use executable helpers to decide branch and build result; use spec count for integer result */
    if contains_space_exec(&txt) {
        let words = split_on_whitespace_exec(&txt);
        SplitResult::StringSeq { words }
    } else if contains_comma_exec(&txt) {
        let words = split_on_comma_exec(&txt);
        SplitResult::StringSeq { words }
    } else {
        SplitResult::Count { value: count_odd_position_lowercase(txt@) }
    }
}

// </vc-code>


}

fn main() {}