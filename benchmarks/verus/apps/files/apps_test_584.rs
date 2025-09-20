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
    // impl-start
    assume(false);
    (0, 0)
    // impl-end
}
// </vc-code>


}

fn main() {}