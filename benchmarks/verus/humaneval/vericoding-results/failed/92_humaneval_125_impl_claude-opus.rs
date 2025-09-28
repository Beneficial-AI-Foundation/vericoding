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
/* helper modified by LLM (iteration 5): No changes needed - spec functions are correct */
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
    /* code modified by LLM (iteration 5): Fix type issues and use Seq directly instead of collect */
    let mut has_space = false;
    let mut has_comma = false;
    
    let mut i = 0;
    while i < txt.len()
        invariant
            0 <= i <= txt.len(),
            has_space == exists|j: int| 0 <= j < i && txt@[j] == ' ',
            has_comma == exists|j: int| 0 <= j < i && txt@[j] == ',',
    {
        if txt[i] == ' ' {
            has_space = true;
        }
        if txt[i] == ',' {
            has_comma = true;
        }
        i = i + 1;
    }
    
    if has_space {
        let mut words = Vec::new();
        let mut current_word = Vec::new();
        let mut i = 0;
        
        while i < txt.len()
            invariant
                0 <= i <= txt.len(),
                words@.len() >= 0,
                current_word@.len() >= 0,
        {
            if txt[i] == ' ' {
                if current_word.len() > 0 {
                    words.push(current_word);
                    current_word = Vec::new();
                }
            } else {
                current_word.push(txt[i]);
            }
            i = i + 1;
        }
        
        if current_word.len() > 0 {
            words.push(current_word);
        }
        
        let ghost result_seq = words@.map(|w: Vec<char>| w@);
        SplitResult::StringSeq { words: result_seq }
    } else if has_comma {
        let mut words = Vec::new();
        let mut current_word = Vec::new();
        let mut i = 0;
        
        while i < txt.len()
            invariant
                0 <= i <= txt.len(),
                words@.len() >= 0,
        {
            if txt[i] == ',' {
                words.push(current_word);
                current_word = Vec::new();
            } else {
                current_word.push(txt[i]);
            }
            i = i + 1;
        }
        
        words.push(current_word);
        let ghost result_seq = words@.map(|w: Vec<char>| w@);
        SplitResult::StringSeq { words: result_seq }
    } else {
        let ghost count_spec = count_odd_position_lowercase(txt@);
        let mut count: u32 = 0;
        let ghost mut count_int: int = 0;
        let mut i = 0;
        
        while i < txt.len()
            invariant
                0 <= i <= txt.len(),
                count >= 0,
                count_int == count as int,
                count_int == count_odd_position_lowercase_helper(txt@, 0) - count_odd_position_lowercase_helper(txt@, i as int),
        {
            let c = txt[i];
            if 'a' <= c && c <= 'z' {
                let pos = (c as u8 - 'a' as u8);
                if pos % 2 == 1 {
                    count = count + 1;
                    proof { count_int = count_int + 1; }
                }
            }
            i = i + 1;
        }
        
        proof {
            assert(count_int == count_spec);
        }
        SplitResult::Count { value: count_int }
    }
}
// </vc-code>


}

fn main() {}