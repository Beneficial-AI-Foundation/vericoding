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

proof fn lemma_find_char_properties(s: Seq<char>, c: char, start: int)
    requires
        0 <= start <= s.len(),
    ensures
        find_char(s, c, start) >= -1,
        find_char(s, c, start) < s.len() || find_char(s, c, start) == -1,
        find_char(s, c, start) >= start || find_char(s, c, start) == -1,
        forall|i: int| start <= i < find_char(s, c, start) ==> s[i] != c,
        find_char(s, c, start) >= 0 ==> s[find_char(s, c, start)] == c,
    decreases s.len() - start
{
    if start >= s.len() {
    } else if s[start] == c {
    } else {
        lemma_find_char_properties(s, c, start + 1);
    }
}

proof fn lemma_rfind_char_properties(s: Seq<char>, c: char)
    ensures
        rfind_char(s, c) >= -1,
        rfind_char(s, c) < s.len() || rfind_char(s, c) == -1,
        forall|i: int| rfind_char(s, c) < i < s.len() ==> s[i] != c,
        rfind_char(s, c) >= 0 ==> s[rfind_char(s, c)] == c,
    decreases s.len()
{
    lemma_rfind_char_helper_properties(s, c, s.len() as int - 1);
}

proof fn lemma_rfind_char_helper_properties(s: Seq<char>, c: char, pos: int)
    requires
        -1 <= pos < s.len(),
    ensures
        rfind_char_helper(s, c, pos) >= -1,
        rfind_char_helper(s, c, pos) <= pos,
        forall|i: int| rfind_char_helper(s, c, pos) < i <= pos ==> s[i] != c,
        rfind_char_helper(s, c, pos) >= 0 ==> s[rfind_char_helper(s, c, pos)] == c,
    decreases pos + 1
{
    if pos < 0 {
    } else if s[pos] == c {
    } else {
        lemma_rfind_char_helper_properties(s, c, pos - 1);
    }
}

proof fn lemma_calculate_balance_nonnegative(s: Seq<char>, pos: int, balance: int)
    requires
        0 <= pos <= s.len(),
        balance >= 0,
    ensures
        calculate_balance_helper(s, pos, balance) >= 0,
    decreases s.len() - pos
{
    if pos >= s.len() {
    } else if s[pos] == 'M' {
        lemma_calculate_balance_nonnegative(s, pos + 1, balance + 1);
    } else {
        lemma_calculate_balance_nonnegative(s, pos + 1, if balance > 0 { balance - 1 } else { 0 });
    }
}

proof fn lemma_count_char_nonnegative(s: Seq<char>, c: char, pos: int, count: nat)
    ensures
        count_char_helper(s, c, pos, count) >= count,
    decreases s.len() - pos
{
    if pos >= s.len() {
    } else if s[pos] == c {
        lemma_count_char_nonnegative(s, c, pos + 1, count + 1);
    } else {
        lemma_count_char_nonnegative(s, c, pos + 1, count);
    }
}

proof fn lemma_nat_to_string_valid(n: nat)
    ensures
        nat_to_string(n).len() >= 1,
        forall|i: int| 0 <= i < nat_to_string(n).len() ==> ('0' <= nat_to_string(n)[i] <= '9'),
        nat_to_string(n)[0] != '0' || n == 0,
    decreases n
{
    if n == 0 {
    } else {
        lemma_nat_to_string_valid(n / 10);
    }
}

/* helper modified by LLM (iteration 5): Fixed usize indexing and bounds checking */
fn find_char_impl(s: &Vec<char>, c: char, start: usize) -> i32 {
    let mut i = start;
    while i < s.len() {
        if s[i] == c {
            return i as i32;
        }
        i += 1;
    }
    -1
}

/* helper modified by LLM (iteration 5): Fixed usize bounds checking */
fn rfind_char_impl(s: &Vec<char>, c: char) -> i32 {
    if s.is_empty() {
        return -1;
    }
    let mut i = (s.len() - 1) as i32;
    while i >= 0 {
        if s[i as usize] == c {
            return i;
        }
        i -= 1;
    }
    -1
}

/* helper modified by LLM (iteration 5): Fixed implementation to match spec behavior */
fn calculate_balance_impl(s: &Vec<char>) -> u32 {
    let mut balance = 0;
    for i in 0..s.len() {
        if s[i] == 'M' {
            balance += 1;
        } else if balance > 0 {
            balance -= 1;
        }
    }
    balance as u32
}

/* helper modified by LLM (iteration 5): Fixed implementation to return correct type */
fn count_char_impl(s: &Vec<char>, c: char) -> u32 {
    let mut count = 0;
    for i in 0..s.len() {
        if s[i] == c {
            count += 1;
        }
    }
    count as u32
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
    /* code modified by LLM (iteration 5): Fixed usize indexing and boundary conditions */
    let rev_input = input.clone().into_iter().rev().collect::<Vec<char>>();
    
    let first_f_index = find_char_impl(&rev_input, 'F', 0);
    if first_f_index == -1 {
        return format!("0\n").chars().collect();
    }
    
    let first_m_after_f_index = find_char_impl(&rev_input, 'M', (first_f_index + 1) as usize);
    if first_m_after_f_index == -1 {
        return format!("0\n").chars().collect();
    }
    
    let last_m_index = rfind_char_impl(&rev_input, 'M');
    if last_m_index < first_m_after_f_index {
        return format!("0\n").chars().collect();
    }
    
    let start_index = first_m_after_f_index as usize;
    let end_index = (last_m_index + 1) as usize;
    
    // Check bounds before slicing
    if start_index >= rev_input.len() || end_index > rev_input.len() || start_index > end_index {
        return format!("0\n").chars().collect();
    }
    
    let substring_vec: Vec<char> = rev_input[start_index..end_index].to_vec();
    
    let balance = calculate_balance_impl(&substring_vec);
    let f_count = count_char_impl(&substring_vec, 'F');
    
    let result_val = if first_m_after_f_index - first_f_index - 1 > 0 {
        balance + f_count + (first_m_after_f_index - first_f_index - 1) as u32
    } else {
        balance + f_count
    };
    
    let mut result_string = format!("{}\n", result_val);
    result_string.chars().collect()
}
// </vc-code>


}

fn main() {}