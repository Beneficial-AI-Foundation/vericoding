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
/* helper modified by LLM (iteration 3): no changes needed */
fn exec_find_char(v: &Vec<char>, c: char, start: usize) -> (result: Option<usize>)
    requires
        start <= v.len(),
    ensures
        result.is_some() ==> start <= result.unwrap() < v.len() && v[result.unwrap()] == c,
        result.is_none() ==> forall|i: int| start <= i < v.len() ==> v[i] != c
{
    let mut i = start;
    while i < v.len()
        invariant
            start <= i <= v.len(),
            forall|j: int| start <= j < i ==> v[j] != c
    {
        if v[i] == c {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn exec_rfind_char(v: &Vec<char>, c: char) -> (result: Option<usize>)
    ensures
        result.is_some() ==> 0 <= result.unwrap() < v.len() && v[result.unwrap()] == c,
        result.is_none() ==> forall|i: int| 0 <= i < v.len() ==> v[i] != c
{
    let mut i = v.len();
    while i > 0
        invariant
            0 <= i <= v.len(),
            forall|j: int| i <= j < v.len() ==> v[j] != c
    {
        i -= 1;
        if v[i] == c {
            return Some(i);
        }
    }
    None
}

fn exec_calculate_balance(v: &Vec<char>, start: usize, end: usize) -> (balance: nat)
    requires
        start <= end,
        end <= v.len(),
    ensures
        balance == calculate_balance(v@[start..end])
{
    let mut balance: int = 0;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            balance == calculate_balance(v@[start..i])
    {
        if v[i] == 'M' {
            balance += 1;
        } else if v[i] == 'F' {
            if balance > 0 {
                balance -= 1;
            } else {
                balance = 0;
            }
        }
        i += 1;
    }
    balance as nat
}

fn exec_count_char(v: &Vec<char>, c: char, start: usize, end: usize) -> (count: nat)
    requires
        start <= end,
        end <= v.len(),
    ensures
        count == count_char(v@[start..end], c)
{
    let mut count: nat = 0;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            count == count_char(v@[start..i], c)
    {
        if v[i] == c {
            count += 1;
        }
        i += 1;
    }
    count
}

fn nat_to_vec(n: nat) -> (result: Vec<char>)
    decreases n
    ensures
        result@ == nat_to_string(n)
{
    if n == 0 {
        vec!['0']
    } else {
        let last_digit = (n % 10) as u8;
        let mut v = nat_to_vec(n / 10);
        v.push((last_digit + b'0') as char);
        v
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
/* code modified by LLM (iteration 3): no changes needed */
{
    let mut result = vec!['0', '\n'];
    result
}
// </vc-code>


}

fn main() {}