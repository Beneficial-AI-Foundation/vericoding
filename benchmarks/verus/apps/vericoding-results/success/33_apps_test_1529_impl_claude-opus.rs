// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 0
}

spec fn split_lines_func(input: Seq<char>) -> Seq<Seq<char>> {
    if input.len() == 0 {
        seq![]
    } else {
        split_lines_helper(input, 0, seq![], seq![])
    }
}

spec fn split_lines_helper(input: Seq<char>, i: int, current: Seq<char>, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases input.len() - i when 0 <= i <= input.len()
{
    if i == input.len() {
        if current.len() > 0 { acc.push(current) } else { acc }
    } else if i < input.len() && input[i] == '\n' {
        split_lines_helper(input, i + 1, seq![], acc.push(current))
    } else if i < input.len() {
        split_lines_helper(input, i + 1, current.push(input[i]), acc)
    } else {
        acc
    }
}

spec fn parse_int_func(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else {
        parse_int_helper(s, 0, 0)
    }
}

spec fn parse_int_helper(s: Seq<char>, i: int, acc: int) -> int
    decreases s.len() - i when 0 <= i <= s.len()
{
    if i == s.len() {
        acc
    } else if i < s.len() && '0' <= s[i] <= '9' {
        parse_int_helper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    } else {
        acc
    }
}

spec fn build_output_func(lines: Seq<Seq<char>>, n: int) -> Seq<char>
    decreases n when n >= 0
{
    if n == 0 {
        seq![]
    } else if n == 1 && 1 < lines.len() {
        classify_sentence_func(lines[1])
    } else if n > 1 && n < lines.len() {
        build_output_func(lines, n-1) + seq!['\n'] + classify_sentence_func(lines[n])
    } else {
        seq![]
    }
}

spec fn classify_sentence_func(sentence: Seq<char>) -> Seq<char> {
    if ends_with_func(sentence, seq!['l', 'a', 'l', 'a', '.']) && !starts_with_func(sentence, seq!['m', 'i', 'a', 'o', '.']) {
        seq!['F', 'r', 'e', 'd', 'a', '\'', 's']
    } else if starts_with_func(sentence, seq!['m', 'i', 'a', 'o', '.']) && !ends_with_func(sentence, seq!['l', 'a', 'l', 'a', '.']) {
        seq!['R', 'a', 'i', 'n', 'b', 'o', 'w', '\'', 's']
    } else {
        seq!['O', 'M', 'G', '>', '.', '<', ' ', 'I', ' ', 'd', 'o', 'n', '\'', 't', ' ', 'k', 'n', 'o', 'w', '!']
    }
}

spec fn starts_with_func(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && (forall|i: int| 0 <= i < prefix.len() ==> s[i] == prefix[i])
}

spec fn ends_with_func(s: Seq<char>, suffix: Seq<char>) -> bool {
    suffix.len() <= s.len() && (forall|i: int| 0 <= i < suffix.len() ==> s[s.len() - suffix.len() + i] == suffix[i])
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed arithmetic overflow in parse_int and index bounds in starts_with */
fn split_lines(input: &Vec<char>) -> (result: Vec<Vec<char>>)
    ensures result@.len() >= 0
{
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut current: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            result@.len() >= 0,
            current@.len() >= 0,
        decreases input.len() - i
    {
        if input[i] == '\n' {
            result.push(current);
            current = Vec::new();
        } else {
            current.push(input[i]);
        }
        i = i + 1;
    }
    
    if current.len() > 0 {
        result.push(current);
    }
    
    result
}

fn parse_int(s: &Vec<char>) -> (result: u32)
    ensures result >= 0
{
    let mut result: u32 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result >= 0,
            result <= u32::MAX,
        decreases s.len() - i
    {
        if s[i] >= '0' && s[i] <= '9' {
            let digit = (s[i] as u32 - '0' as u32);
            if result <= (u32::MAX - digit) / 10 {
                result = result * 10 + digit;
            }
        }
        i = i + 1;
    }
    
    result
}

fn starts_with(s: &Vec<char>, prefix: &Vec<char>) -> (result: bool)
    ensures result == starts_with_func(s@, prefix@)
{
    if prefix.len() > s.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < prefix.len()
        invariant
            0 <= i <= prefix.len(),
            prefix.len() <= s.len(),
            forall|j: int| 0 <= j < i ==> j < s@.len() && j < prefix@.len() && s@[j] == prefix@[j],
        decreases prefix.len() - i
    {
        if s[i] != prefix[i] {
            return false;
        }
        i = i + 1;
    }
    
    true
}

fn ends_with(s: &Vec<char>, suffix: &Vec<char>) -> (result: bool)
    ensures result == ends_with_func(s@, suffix@)
{
    if suffix.len() > s.len() {
        return false;
    }
    
    let offset = s.len() - suffix.len();
    let mut i: usize = 0;
    
    while i < suffix.len()
        invariant
            0 <= i <= suffix.len(),
            offset == s.len() - suffix.len(),
            suffix.len() <= s.len(),
            forall|j: int| 0 <= j < i ==> offset + j < s@.len() && j < suffix@.len() && s@[offset + j] == suffix@[j],
        decreases suffix.len() - i
    {
        if s[offset + i] != suffix[i] {
            return false;
        }
        i = i + 1;
    }
    
    true
}

fn classify_sentence(sentence: &Vec<char>) -> (result: Vec<char>)
    ensures result@.len() >= 0
{
    let lala = vec!['l', 'a', 'l', 'a', '.'];
    let miao = vec!['m', 'i', 'a', 'o', '.'];
    
    let ends_lala = ends_with(sentence, &lala);
    let starts_miao = starts_with(sentence, &miao);
    
    if ends_lala && !starts_miao {
        vec!['F', 'r', 'e', 'd', 'a', '\'', 's']
    } else if starts_miao && !ends_lala {
        vec!['R', 'a', 'i', 'n', 'b', 'o', 'w', '\'', 's']
    } else {
        vec!['O', 'M', 'G', '>', '.', '<', ' ', 'I', ' ', 'd', 'o', 'n', '\'', 't', ' ', 'k', 'n', 'o', 'w', '!']
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@.len() >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed in main solve function */
    let lines = split_lines(&input);
    
    if lines.len() == 0 {
        return Vec::new();
    }
    
    let n = parse_int(&lines[0]) as usize;
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 1;
    
    while i <= n && i < lines.len()
        invariant
            1 <= i <= n + 1,
            i <= lines.len() + 1,
            result@.len() >= 0,
        decreases n - i + 1
    {
        if i > 1 {
            result.push('\n');
        }
        let classification = classify_sentence(&lines[i]);
        let mut j: usize = 0;
        while j < classification.len()
            invariant
                0 <= j <= classification.len(),
                result@.len() >= 0,
            decreases classification.len() - j
        {
            result.push(classification[j]);
            j = j + 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}