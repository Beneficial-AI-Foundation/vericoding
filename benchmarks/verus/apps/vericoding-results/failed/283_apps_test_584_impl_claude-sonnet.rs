// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_letter(c: char) -> bool {
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

spec fn valid_parentheses(input: Seq<char>) -> bool {
    let newline_pos = find_newline(input);
    if newline_pos >= input.len() {
        true
    } else {
        let s = if newline_pos + 1 < input.len() { 
            input.subrange(newline_pos + 1, input.len() as int) 
        } else { 
            seq![] 
        };
        is_valid_parentheses_sequence(s, 0, 0)
    }
}

spec fn is_valid_parentheses_sequence(s: Seq<char>, pos: int, balance: int) -> bool
    recommends 0 <= pos <= s.len(), balance >= 0
    decreases s.len() - pos
{
    if pos >= s.len() {
        balance == 0
    } else {
        let c = s[pos];
        let new_balance = if c == '(' { 
            balance + 1 
        } else if c == ')' { 
            balance - 1 
        } else { 
            balance 
        };
        new_balance >= 0 && is_valid_parentheses_sequence(s, pos + 1, new_balance)
    }
}

spec fn longest_word_outside(input: Seq<char>) -> int {
    let newline_pos = find_newline(input);
    if newline_pos >= input.len() {
        0
    } else {
        let s = if newline_pos + 1 < input.len() { 
            input.subrange(newline_pos + 1, input.len() as int) 
        } else { 
            seq![] 
        };
        compute_longest_outside(s, 0, 0, 0, 0)
    }
}

spec fn count_words_inside(input: Seq<char>) -> int {
    let newline_pos = find_newline(input);
    if newline_pos >= input.len() {
        0
    } else {
        let s = if newline_pos + 1 < input.len() { 
            input.subrange(newline_pos + 1, input.len() as int) 
        } else { 
            seq![] 
        };
        compute_count_inside(s, 0, 0, 0)
    }
}

spec fn valid_output(input: Seq<char>, len_out: int, count_in: int) -> bool {
    len_out >= 0 && count_in >= 0 &&
    len_out == longest_word_outside(input) &&
    count_in == count_words_inside(input)
}

spec fn find_newline(input: Seq<char>) -> int {
    find_newline_helper(input, 0)
}

spec fn find_newline_helper(input: Seq<char>, pos: int) -> int
    recommends 0 <= pos <= input.len()
    decreases input.len() - pos
{
    if pos >= input.len() {
        pos
    } else if input[pos] == '\n' {
        pos
    } else {
        find_newline_helper(input, pos + 1)
    }
}

spec fn compute_longest_outside(s: Seq<char>, pos: int, balance: int, cur: int, best: int) -> int
    recommends 0 <= pos <= s.len(), balance >= 0, cur >= 0, best >= 0
    decreases s.len() - pos
{
    if pos >= s.len() {
        if cur > best && balance == 0 { cur } else { best }
    } else {
        let c = s[pos];
        let new_balance = if c == '(' { 
            balance + 1 
        } else if c == ')' { 
            if balance > 0 { balance - 1 } else { 0 }
        } else { 
            balance 
        };
        let new_cur = if is_letter(c) { 
            cur + 1
        } else if cur > 0 { 
            0
        } else { 
            cur 
        };
        let new_best = if !is_letter(c) && cur > 0 && balance == 0 {
            if cur > best { cur } else { best }
        } else { 
            best 
        };
        compute_longest_outside(s, pos + 1, new_balance, new_cur, new_best)
    }
}

spec fn compute_count_inside(s: Seq<char>, pos: int, balance: int, cur: int) -> int
    recommends 0 <= pos <= s.len(), balance >= 0, cur >= 0
    decreases s.len() - pos
{
    if pos >= s.len() {
        0
    } else {
        let c = s[pos];
        let new_balance = if c == '(' { 
            balance + 1 
        } else if c == ')' { 
            if balance > 0 { balance - 1 } else { 0 }
        } else { 
            balance 
        };
        let new_cur = if is_letter(c) { 
            cur + 1
        } else if cur > 0 { 
            0
        } else { 
            cur 
        };
        let word_ended = !is_letter(c) && cur > 0;
        let count_increment: int = if word_ended && balance > 0 { 1 } else { 0 };
        count_increment + compute_count_inside(s, pos + 1, new_balance, new_cur)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix arithmetic overflow and ensure postconditions match spec functions */
fn is_letter_exec(c: char) -> (result: bool)
    ensures result == is_letter(c)
{
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

fn find_newline_impl(input: &Vec<char>) -> (pos: usize)
    requires
        input@.len() > 0,
        exists|i: int| 0 <= i < input@.len() && input@[i] == '
'
    ensures
        pos < input@.len(),
        input@[pos as int] == '
',
        pos as int == find_newline(input@)
{
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input@.len(),
            forall|j: int| 0 <= j < i ==> input@[j] != '
'
        decreases input@.len() - i
    {
        if input[i] == '
' {
            return i;
        }
        i += 1;
    }
    proof {
        assert(false);
    }
    0
}

fn process_after_newline(input: &Vec<char>, start: usize) -> (result: (usize, usize))
    requires
        start < input@.len(),
        input@[start as int] == '
',
        start as int == find_newline(input@),
        valid_parentheses(input@),
        start + 1 <= usize::MAX
    ensures
        result.0 as int == longest_word_outside(input@),
        result.1 as int == count_words_inside(input@)
{
    if start >= usize::MAX {
        return (0, 0);
    }
    if start + 1 >= input.len() {
        return (0, 0);
    }
    
    let mut pos = start + 1;
    let mut balance: i32 = 0;
    let mut current_word_len: usize = 0;
    let mut longest_outside: usize = 0;
    let mut words_inside: i32 = 0;
    
    while pos < input.len()
        invariant
            start + 1 <= pos <= input@.len(),
            balance >= 0,
            current_word_len >= 0,
            longest_outside >= 0,
            words_inside >= 0,
            balance <= i32::MAX,
            words_inside <= i32::MAX
        decreases input@.len() - pos
    {
        let c = input[pos];
        
        if c == '(' {
            if current_word_len > 0 && balance == 0 {
                if current_word_len > longest_outside {
                    longest_outside = current_word_len;
                }
                current_word_len = 0;
            } else if current_word_len > 0 {
                current_word_len = 0;
            }
            if balance < i32::MAX {
                balance = balance + 1;
            }
        } else if c == ')' {
            if current_word_len > 0 {
                if balance > 0 && words_inside < i32::MAX {
                    words_inside = words_inside + 1;
                }
                current_word_len = 0;
            }
            if balance > 0 {
                balance = balance - 1;
            }
        } else if is_letter_exec(c) {
            current_word_len = current_word_len + 1;
        } else {
            if current_word_len > 0 {
                if balance == 0 {
                    if current_word_len > longest_outside {
                        longest_outside = current_word_len;
                    }
                } else if words_inside < i32::MAX {
                    words_inside = words_inside + 1;
                }
                current_word_len = 0;
            }
        }
        
        pos = pos + 1;
    }
    
    if current_word_len > 0 && balance == 0 {
        if current_word_len > longest_outside {
            longest_outside = current_word_len;
        }
    }
    
    (longest_outside, words_inside as usize)
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: (usize, usize))
    requires
        input@.len() > 0,
        exists|i: int| 0 <= i < input@.len() && input@[i] == '\n',
        forall|i: int| 0 <= i < input@.len() ==> (is_letter(input@[i]) || input@[i] == '_' || input@[i] == '(' || input@[i] == ')' || input@[i] == '\n' || input@[i] == '\r' || ('0' <= input@[i] <= '9')),
        valid_parentheses(input@)
    ensures
        result.0 >= 0 && result.1 >= 0,
        result.0 as int == longest_word_outside(input@),
        result.1 as int == count_words_inside(input@),
        valid_output(input@, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix precondition for helper function */
    let newline_pos = find_newline_impl(&input);
    proof {
        assert(newline_pos + 1 <= usize::MAX);
    }
    let result = process_after_newline(&input, newline_pos);
    result
}
// </vc-code>


}

fn main() {}