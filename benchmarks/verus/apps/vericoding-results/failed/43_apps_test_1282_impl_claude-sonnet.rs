// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 1 && forall|i: int| 0 <= i < input.len() ==> input[i] == 'M' || input[i] == 'F'
}

spec fn compute_swap_time(input: Seq<char>) -> nat
    recommends valid_input(input)
{
    let rev_input = input.reverse();
    let first_f = find_char(rev_input, 'F', 0);

    if first_f == -1 { 0nat }
    else {
        let first_m_after_f = find_char(rev_input, 'M', first_f + 1);
        if first_m_after_f == -1 { 0nat }
        else {
            let last_m = rfind_char(rev_input, 'M');
            if last_m < first_m_after_f { 0nat }
            else {
                let substring = rev_input.subrange(first_m_after_f, last_m + 1);
                let balance = calculate_balance(substring);
                let f_count = count_char(substring, 'F');
                (balance + f_count + first_m_after_f - first_f - 1) as nat
            }
        }
    }
}
spec fn find_char(s: Seq<char>, c: char, start: int) -> int
    decreases s.len() - start
{
    if start >= s.len() { -1 }
    else if s[start] == c { start }
    else { find_char(s, c, start + 1) }
}

spec fn rfind_char(s: Seq<char>, c: char) -> int {
    rfind_char_helper(s, c, s.len() as int - 1)
}

spec fn rfind_char_helper(s: Seq<char>, c: char, pos: int) -> int
    decreases pos + 1
{
    if pos < 0 { -1 }
    else if s[pos] == c { pos }
    else { rfind_char_helper(s, c, pos - 1) }
}

spec fn calculate_balance(s: Seq<char>) -> nat {
    calculate_balance_helper(s, 0, 0)
}

spec fn calculate_balance_helper(s: Seq<char>, pos: int, balance: int) -> nat
    decreases s.len() - pos
{
    if pos >= s.len() { balance as nat }
    else if s[pos] == 'M' { calculate_balance_helper(s, pos + 1, balance + 1) }
    else { calculate_balance_helper(s, pos + 1, if balance > 0 { balance - 1 } else { 0 }) }
}

spec fn count_char(s: Seq<char>, c: char) -> nat {
    count_char_helper(s, c, 0, 0)
}

spec fn count_char_helper(s: Seq<char>, c: char, pos: int, count: nat) -> nat
    decreases s.len() - pos
{
    if pos >= s.len() { count }
    else if s[pos] == c { count_char_helper(s, c, pos + 1, count + 1) }
    else { count_char_helper(s, c, pos + 1, count) }
}

spec fn nat_to_string(n: nat) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else { nat_to_string_helper(n, seq![]) }
}

spec fn nat_to_string_helper(n: nat, acc: Seq<char>) -> Seq<char>
    decreases n
{
    if n == 0 { acc }
    else { nat_to_string_helper(n / 10, seq![('0' as u8 + (n % 10) as u8) as char] + acc) }
}
// </vc-preamble>

// <vc-helpers>
fn find_char_exec(s: &Vec<char>, c: char, start: usize) -> (result: i32)
    requires
        start <= s@.len(),
    ensures
        result == find_char(s@, c, start as int),
{
    let mut i = start;
    while i < s.len()
        invariant
            start <= i <= s@.len(),
            find_char(s@, c, start as int) == find_char(s@, c, i as int),
    {
        if s[i] == c {
            return i as i32;
        }
        i += 1;
    }
    -1
}

fn rfind_char_exec(s: &Vec<char>, c: char) -> (result: i32)
    requires
        s@.len() >= 1,
    ensures
        result == rfind_char(s@, c),
{
    let mut i = s.len() - 1;
    loop
        invariant
            i < s@.len(),
            rfind_char(s@, c) == rfind_char_helper(s@, c, i as int),
    {
        if s[i] == c {
            return i as i32;
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }
    -1
}

fn calculate_balance_exec(s: &Vec<char>) -> (result: u32)
    ensures
        result == calculate_balance(s@),
{
    let mut balance = 0i32;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            balance >= 0,
            balance as nat == calculate_balance_helper(s@.subrange(0, i as int), 0, 0),
    {
        if s[i] == 'M' {
            balance += 1;
        } else if balance > 0 {
            balance -= 1;
        }
        i += 1;
    }
    balance as u32
}

fn count_char_exec(s: &Vec<char>, c: char) -> (result: u32)
    ensures
        result == count_char(s@, c),
{
    let mut count = 0u32;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            count == count_char_helper(s@, c, 0, 0).spec_sub(count_char_helper(s@, c, i as int, 0)),
    {
        if s[i] == c {
            count += 1;
        }
        i += 1;
    }
    count
}

/* helper modified by LLM (iteration 5): use simpler approach without complex reverse operation */
fn nat_to_string_exec(n: u32) -> (result: Vec<char>)
    ensures
        result@ == nat_to_string(n as nat),
{
    if n == 0 {
        vec!['0']
    } else {
        let mut digits = Vec::new();
        let mut num = n;
        while num > 0
            invariant
                digits@.len() < 20,
        {
            let digit = (num % 10) as u8 + 48u8;
            digits.push(digit as char);
            num /= 10;
        }
        let mut result = Vec::new();
        let mut i = digits.len();
        while i > 0
            invariant
                i <= digits.len(),
        {
            i -= 1;
            result.push(digits[i]);
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(input@)
    ensures 
        result@.len() >= 1,
        result@[result@.len() - 1] == '\n',
        exists|val: nat| val >= 0 && result@ == nat_to_string(val) + seq!['\n'],
        result@ == nat_to_string(compute_swap_time(input@)) + seq!['\n']
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid calling reverse on complex expression */
    let mut rev_input = input.clone();
    let rev_len = rev_input.len();
    let mut i = 0;
    while i < rev_len / 2
        invariant
            i <= rev_len / 2,
    {
        let temp = rev_input[i];
        rev_input.set(i, rev_input[rev_len - 1 - i]);
        rev_input.set(rev_len - 1 - i, temp);
        i += 1;
    }
    
    let first_f = find_char_exec(&rev_input, 'F', 0);
    
    if first_f == -1 {
        let mut result = nat_to_string_exec(0);
        result.push('\n');
        return result;
    }
    
    let first_m_after_f = find_char_exec(&rev_input, 'M', (first_f + 1) as usize);
    
    if first_m_after_f == -1 {
        let mut result = nat_to_string_exec(0);
        result.push('\n');
        return result;
    }
    
    let last_m = rfind_char_exec(&rev_input, 'M');
    
    if last_m < first_m_after_f {
        let mut result = nat_to_string_exec(0);
        result.push('\n');
        return result;
    }
    
    let mut substring = Vec::new();
    let mut i = first_m_after_f as usize;
    while i <= last_m as usize
        invariant
            first_m_after_f as usize <= i <= last_m as usize + 1,
    {
        substring.push(rev_input[i]);
        i += 1;
    }
    
    let balance = calculate_balance_exec(&substring);
    let f_count = count_char_exec(&substring, 'F');
    let swap_time = balance + f_count + (first_m_after_f - first_f - 1) as u32;
    
    let mut result = nat_to_string_exec(swap_time);
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}