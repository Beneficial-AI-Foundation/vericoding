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
/* helper modified by LLM (iteration 5): Fixed postcondition and cast issues in all helper functions */
fn find_char_exec(s: &Vec<char>, c: char, start: usize) -> (result: isize)
    requires
        start <= s.len()
    ensures
        result == find_char(s@, c, start as int)
    decreases s.len() - start
{
    if start >= s.len() {
        -1
    } else if s[start] == c {
        proof {
            assert(start < s.len());
            assert(start <= isize::MAX as usize);
        }
        start as isize
    } else {
        find_char_exec(s, c, start + 1)
    }
}

fn rfind_char_exec(s: &Vec<char>, c: char) -> (result: isize)
    ensures
        result == rfind_char(s@, c)
{
    if s.len() == 0 {
        -1
    } else {
        proof {
            assert(s.len() - 1 < s.len());
            assert(s.len() - 1 <= isize::MAX as usize);
        }
        rfind_char_helper_exec(s, c, (s.len() - 1) as isize)
    }
}

fn rfind_char_helper_exec(s: &Vec<char>, c: char, pos: isize) -> (result: isize)
    requires
        pos < s.len() as isize,
        pos >= -1,
        s.len() <= isize::MAX as usize
    ensures
        result == rfind_char_helper(s@, c, pos as int)
    decreases pos + 1
{
    if pos < 0 {
        -1
    } else if s[pos as usize] == c {
        pos
    } else {
        rfind_char_helper_exec(s, c, pos - 1)
    }
}

fn calculate_balance_exec(s: &Vec<char>) -> (result: usize)
    ensures
        result == calculate_balance(s@)
{
    calculate_balance_helper_exec(s, 0, 0)
}

fn calculate_balance_helper_exec(s: &Vec<char>, pos: usize, balance: isize) -> (result: usize)
    requires
        pos <= s.len(),
        balance >= 0,
        balance <= pos as isize,
        pos <= isize::MAX as usize
    ensures
        result == calculate_balance_helper(s@, pos as int, balance as int)
    decreases s.len() - pos
{
    if pos >= s.len() {
        balance as usize
    } else if s[pos] == 'M' {
        proof {
            assert(pos + 1 <= s.len());
            assert(pos + 1 <= isize::MAX as usize);
            assert(balance >= 0);
            assert(balance <= pos as isize);
            assert(balance + 1 <= pos as isize + 1);
        }
        calculate_balance_helper_exec(s, pos + 1, balance + 1)
    } else {
        let new_balance = if balance > 0 { balance - 1 } else { 0 };
        proof {
            assert(new_balance >= 0);
            assert(pos + 1 <= isize::MAX as usize);
            assert(new_balance <= pos as isize + 1);
        }
        calculate_balance_helper_exec(s, pos + 1, new_balance)
    }
}

fn count_char_exec(s: &Vec<char>, c: char) -> (result: usize)
    ensures
        result == count_char(s@, c)
{
    count_char_helper_exec(s, c, 0, 0)
}

fn count_char_helper_exec(s: &Vec<char>, c: char, pos: usize, count: usize) -> (result: usize)
    requires
        pos <= s.len(),
        count <= pos
    ensures
        result == count_char_helper(s@, c, pos as int, count as nat)
    decreases s.len() - pos
{
    if pos >= s.len() {
        count
    } else if s[pos] == c {
        proof {
            assert(count + 1 <= pos + 1);
        }
        count_char_helper_exec(s, c, pos + 1, count + 1)
    } else {
        proof {
            assert(count <= pos + 1);
        }
        count_char_helper_exec(s, c, pos + 1, count)
    }
}

fn nat_to_vec_helper(n: usize, acc: Vec<char>) -> (result: Vec<char>)
    ensures
        result@ == nat_to_string_helper(n as nat, acc@)
    decreases n
{
    if n == 0 {
        acc
    } else {
        let digit = (n % 10) as u8;
        let mut new_acc = Vec::new();
        new_acc.push(('0' as u8 + digit) as char);
        let mut i = 0;
        while i < acc.len()
            invariant
                i <= acc.len(),
                new_acc.len() == i + 1,
                new_acc@[0] == ('0' as u8 + digit) as char,
                forall|j: int| 1 <= j < new_acc.len() ==> new_acc@[j] == acc@[j - 1]
            decreases acc.len() - i
        {
            new_acc.push(acc[i]);
            i = i + 1;
        }
        proof {
            assert(new_acc@ == seq![('0' as u8 + digit) as char] + acc@);
            assert(nat_to_string_helper(n as nat, acc@) == nat_to_string_helper(n as nat / 10, seq![('0' as u8 + (n as nat % 10) as u8) as char] + acc@));
        }
        nat_to_vec_helper(n / 10, new_acc)
    }
}

fn nat_to_vec(n: usize) -> (result: Vec<char>)
    ensures
        result@ == nat_to_string(n as nat)
{
    if n == 0 {
        vec!['0']
    } else {
        nat_to_vec_helper(n, Vec::new())
    }
}

fn subrange_exec(s: &Vec<char>, start: usize, end: usize) -> (result: Vec<char>)
    requires
        start <= end,
        end <= s.len()
    ensures
        result@ == s@.subrange(start as int, end as int)
{
    let mut result = Vec::new();
    let mut i = start;
    while i < end
        invariant
            start <= i,
            i <= end,
            end <= s.len(),
            result.len() == i - start,
            forall|j: int| 0 <= j < result.len() ==> result@[j] == s@[start + j]
        decreases end - i
    {
        result.push(s[i]);
        i = i + 1;
        proof {
            assert(result@.subrange(0, result.len() - 1) == s@.subrange(start as int, (i - 1) as int));
            assert(result@[result.len() - 1] == s@[i - 1]);
        }
    }
    proof {
        assert(result@ =~= s@.subrange(start as int, end as int));
    }
    result
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
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow issues and bounds checking */
    let mut rev_input = Vec::new();
    let mut i = input.len();
    while i > 0
        invariant
            i <= input.len(),
            rev_input@ == input@.subrange((i as int), (input.len() as int)).reverse()
        decreases i
    {
        i = i - 1;
        rev_input.push(input[i]);
    }
    assert(rev_input@ == input@.reverse());
    
    let first_f = find_char_exec(&rev_input, 'F', 0);
    
    if first_f == -1 {
        let mut result = vec!['0', '\n'];
        proof {
            assert(result@ == nat_to_string(0) + seq!['\n']);
            assert(exists|val: nat| val >= 0 && result@ == nat_to_string(val) + seq!['\n']);
        }
        return result;
    }
    
    if first_f < 0 || first_f >= rev_input.len() as isize {
        let mut result = vec!['0', '\n'];
        proof {
            assert(result@ == nat_to_string(0) + seq!['\n']);
            assert(exists|val: nat| val >= 0 && result@ == nat_to_string(val) + seq!['\n']);
        }
        return result;
    }
    
    let next_pos = first_f + 1;
    if next_pos < 0 || next_pos > rev_input.len() as isize {
        let mut result = vec!['0', '\n'];
        proof {
            assert(result@ == nat_to_string(0) + seq!['\n']);
            assert(exists|val: nat| val >= 0 && result@ == nat_to_string(val) + seq!['\n']);
        }
        return result;
    }
    
    let first_m_after_f = find_char_exec(&rev_input, 'M', next_pos as usize);
    
    if first_m_after_f == -1 {
        let mut result = vec!['0', '\n'];
        proof {
            assert(result@ == nat_to_string(0) + seq!['\n']);
            assert(exists|val: nat| val >= 0 && result@ == nat_to_string(val) + seq!['\n']);
        }
        return result;
    }
    
    let last_m = rfind_char_exec(&rev_input, 'M');
    
    if last_m < first_m_after_f {
        let mut result = vec!['0', '\n'];
        proof {
            assert(result@ == nat_to_string(0) + seq!['\n']);
            assert(exists|val: nat| val >= 0 && result@ == nat_to_string(val) + seq!['\n']);
        }
        return result;
    }
    
    if first_m_after_f < 0 || last_m < 0 || first_m_after_f as usize > rev_input.len() || (last_m + 1) as usize > rev_input.len() {
        let mut result = vec!['0', '\n'];
        proof {
            assert(result@ == nat_to_string(0) + seq!['\n']);
            assert(exists|val: nat| val >= 0 && result@ == nat_to_string(val) + seq!['\n']);
        }
        return result;
    }
    
    let substring = subrange_exec(&rev_input, first_m_after_f as usize, (last_m + 1) as usize);
    let balance = calculate_balance_exec(&substring);
    let f_count = count_char_exec(&substring, 'F');
    
    if first_m_after_f <= first_f {
        let mut result = vec!['0', '\n'];
        proof {
            assert(result@ == nat_to_string(0) + seq!['\n']);
            assert(exists|val: nat| val >= 0 && result@ == nat_to_string(val) + seq!['\n']);
        }
        return result;
    }
    
    let swap_time = balance + f_count + (first_m_after_f - first_f - 1) as usize;
    
    let mut result = nat_to_vec(swap_time);
    result.push('\n');
    proof {
        assert(result@ == nat_to_string(swap_time as nat) + seq!['\n']);
        assert(swap_time as nat == compute_swap_time(input@));
        assert(exists|val: nat| val >= 0 && result@ == nat_to_string(val) + seq!['\n']);
    }
    result
}
// </vc-code>


}

fn main() {}