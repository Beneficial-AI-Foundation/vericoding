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
fn compute_longest_outside_nonneg(s: Seq<char>, pos: int, balance: int, cur: int, best: int)
    requires 0 <= pos <= s.len(), balance >= 0, cur >= 0, best >= 0
    ensures compute_longest_outside(s, pos, balance, cur, best) >= 0
    decreases s.len() - pos
{
    if pos >= s.len() {
        // base case: compute_longest_outside returns either cur or best, both >= 0
    } else {
        let c = s[pos];
        let new_balance = if c == '(' { balance + 1 } else if c == ')' { if balance > 0 { balance - 1 } else { 0 } } else { balance };
        let new_cur = if is_letter(c) { cur + 1 } else if cur > 0 { 0 } else { cur };
        let new_best = if !is_letter(c) && cur > 0 && balance == 0 {
            if cur > best { cur } else { best }
        } else { best };
        compute_longest_outside_nonneg(s, pos + 1, new_balance, new_cur, new_best);
    }
}

fn compute_count_inside_nonneg(s: Seq<char>, pos: int, balance: int, cur: int)
    requires 0 <= pos <= s.len(), balance >= 0, cur >= 0
    ensures compute_count_inside(s, pos, balance, cur) >= 0
    decreases s.len() - pos
{
    if pos >= s.len() {
        // returns 0
    } else {
        let c = s[pos];
        let new_balance = if c == '(' { balance + 1 } else if c == ')' { if balance > 0 { balance - 1 } else { 0 } } else { balance };
        let new_cur = if is_letter(c) { cur + 1 } else if cur > 0 { 0 } else { cur };
        compute_count_inside_nonneg(s, pos + 1, new_balance, new_cur);
    }
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
    // impl-start
    let input_seq: Seq<char> = input@;
    let nl: int = find_newline(input_seq);
    let n: int = input_seq.len();
    let start: int = nl + 1;
    let s: Seq<char> = if start < n { input_seq.subrange(start, n) } else { seq![] };

    let mut pos: int = 0;
    let mut balance: int = 0;
    let mut cur: int = 0;
    let mut best: int = 0;
    let mut count: int = 0;

    while pos < s.len()
        invariant
            0 <= pos <= s.len(),
            balance >= 0,
            cur >= 0,
            best >= 0,
            count >= 0,
            compute_longest_outside(s, pos, balance, cur, best) == compute_longest_outside(s, 0, 0, 0, 0),
            count + compute_count_inside(s, pos, balance, cur) == compute_count_inside(s, 0, 0, 0),
        decreases s.len() - pos
    {
        let c = s[pos];
        let word_ended = !is_letter(c) && cur > 0;
        let count_inc: int = if word_ended && balance > 0 { 1 } else { 0 };
        let new_balance = if c == '(' { balance + 1 } else if c == ')' { if balance > 0 { balance - 1 } else { 0 } } else { balance };
        let new_cur = if is_letter(c) { cur + 1 } else if cur > 0 { 0 } else { cur };
        let new_best = if word_ended && balance == 0 {
            if cur > best { cur } else { best }
        } else { best };

        count = count + count_inc;
        balance = new_balance;
        cur = new_cur;
        best = new_best;
        pos = pos + 1;
    }

    let final_best: int = if cur > best && balance == 0 { cur } else { best };
    (final_best as usize, count as usize)
    // impl-end
}

// </vc-code>


}

fn main() {}