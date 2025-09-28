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
/* code modified by LLM (iteration 5): Corrected type casting errors for `nat` and `int` when used with array indexing and within computations where concrete `usize` is required. Changed `as nat` and `as int` to `as usize` for array indexing, and `int` variables in computations to `usize` for concrete values. */
{
    let s_orig = input@;
    let rev_s = s_orig.reverse();

    let mut first_f_idx: int = -1;
    let mut i: usize = 0;
    while (i as int) < rev_s.len()
        invariant
            0 <= i as int <= rev_s.len(),
            first_f_idx == -1 || (0 <= first_f_idx < i as int && rev_s[first_f_idx as nat] == 'F' && (forall|j: int| 0 <= j < first_f_idx ==> rev_s[j as nat] != 'F')),
            first_f_idx == find_char(rev_s, 'F', 0) || (find_char(rev_s, 'F', 0) == -1 && forall|j: int| 0 <= j < i as int ==> rev_s[j as nat] != 'F'),
        decreases (rev_s.len() as int) - (i as int)
    {
        if rev_s.len() > 0 && i < rev_s.len() && rev_s[i as nat] == 'F' {
            first_f_idx = i as int;
            proof {
                assert(find_char(rev_s, 'F', 0) == first_f_idx);
            }
            break;
        }
        i = i + 1;
    }

    if first_f_idx == -1 {
        let time = 0nat;
        let s = nat_to_string(time);
        let mut result = Vec::new();
        let mut j: usize = 0;
        while (j as int) < s.len()
            invariant
                0 <= j as int <= s.len(),
                result.len() == j,
                forall|k: int| 0 <= k < (j as int) ==> s[k as nat] == result[k as nat],
            decreases (s.len() as int) - (j as int)
        {
            result.push(s[j as nat]);
            j = j + 1;
        }
        result.push('
');
        return result;
    }

    let mut first_m_after_f_idx: int = -1;
    i = (first_f_idx + 1) as usize;
    while (i as int) < rev_s.len()
        invariant
            (first_f_idx + 1) as int <= i as int <= rev_s.len(),
            first_m_after_f_idx == -1 || (first_f_idx + 1 <= first_m_after_f_idx < i as int && rev_s[first_m_after_f_idx as nat] == 'M' && (forall|j: int| (first_f_idx + 1) <= j < first_m_after_f_idx ==> rev_s[j as nat] != 'M')),
            first_m_after_f_idx == find_char(rev_s, 'M', first_f_idx + 1) || (find_char(rev_s, 'M', first_f_idx + 1) == -1 && forall|j: int| (first_f_idx + 1) <= j < i as int ==> rev_s[j as nat] != 'M'),
        decreases (rev_s.len() as int) - (i as int)
    {
        if rev_s.len() > 0 && i < rev_s.len() && rev_s[i as nat] == 'M' {
            first_m_after_f_idx = i as int;
            proof {
                assert(find_char(rev_s, 'M', first_f_idx + 1) == first_m_after_f_idx);
            }
            break;
        }
        i = i + 1;
    }

    if first_m_after_f_idx == -1 {
        let time = 0nat;
        let s_str = nat_to_string(time);
        let mut result = Vec::new();
        let mut j: usize = 0;
        while (j as int) < s_str.len()
            invariant
                0 <= j as int <= s_str.len(),
                result.len() == j,
                forall|k: int| 0 <= k < (j as int) ==> s_str[k as nat] == result[k as nat],
            decreases (s_str.len() as int) - (j as int)
        {
            result.push(s_str[j as nat]);
            j = j + 1;
        }
        result.push('
');
        return result;
    }

    let mut last_m_idx: int = -1;
    let mut i_int: int = rev_s.len() as int - 1;
    while i_int >= 0
        invariant
            -1 <= i_int < rev_s.len(),
            last_m_idx == -1 || (i_int < last_m_idx < rev_s.len() && rev_s[last_m_idx as nat] == 'M' && (forall|j: int| last_m_idx < j < rev_s.len() ==> rev_s[j as nat] != 'M')),
            last_m_idx == rfind_char(rev_s, 'M') || (rfind_char(rev_s, 'M') == -1 && forall|j: int| i_int < j < rev_s.len() ==> rev_s[j as nat] != 'M'),
        decreases i_int + 1
    {
        if rev_s.len() > 0 && i_int >= 0 && (i_int as usize) < rev_s.len() && rev_s[i_int as nat] == 'M' {
            last_m_idx = i_int;
            proof {
                assert(rfind_char(rev_s, 'M') == last_m_idx);
            }
            break;
        }
        i_int = i_int - 1;
    }

    if last_m_idx < first_m_after_f_idx {
        let time = 0nat;
        let s_str = nat_to_string(time);
        let mut result = Vec::new();
        let mut j: usize = 0;
        while (j as int) < s_str.len()
            invariant
                0 <= j as int <= s_str.len(),
                result.len() == j,
                forall|k: int| 0 <= k < (j as int) ==> s_str[k as nat] == result[k as nat],
            decreases (s_str.len() as int) - (j as int)
        {
            result.push(s_str[j as nat]);
            j = j + 1;
        }
        result.push('
');
        return result;
    }

    let mut bal: int = 0;
    let mut f_count_concrete: usize = 0;

    let mut current_idx_int: int = first_m_after_f_idx;
    while current_idx_int <= last_m_idx
        invariant
            first_m_after_f_idx <= current_idx_int <= last_m_idx + 1,
            (first_m_after_f_idx <= current_idx_int ==> bal as nat == calculate_balance(rev_s.subrange(first_m_after_f_idx, current_idx_int as nat))),
            (first_m_after_f_idx <= current_idx_int ==> f_count_concrete as nat == count_char(rev_s.subrange(first_m_after_f_idx, current_idx_int as nat), 'F')),
        decreases (last_m_idx + 1) - current_idx_int
    {
        if rev_s[current_idx_int as nat] == 'M' {
            bal = bal + 1;
        } else {
            if bal > 0 {
                bal = bal - 1;
            } else {
                bal = 0;
            }
            f_count_concrete = f_count_concrete + 1;
        }
        current_idx_int = current_idx_int + 1;
    }
    proof {
        assert(bal as nat == calculate_balance(rev_s.subrange(first_m_after_f_idx, last_m_idx + 1)));
        assert(f_count_concrete as nat == count_char(rev_s.subrange(first_m_after_f_idx, last_m_idx + 1), 'F'));
    }

    let time = (bal as nat + f_count_concrete as nat + (first_m_after_f_idx - first_f_idx - 1) as nat);

    let s_str = nat_to_string(time);

    let mut result = Vec::new();
    let mut j: usize = 0;
    while (j as int) < s_str.len()
        invariant
            0 <= j as int <= s_str.len(),
            result.len() == j,
            forall|k: int| 0 <= k < (j as int) ==> s_str[k as nat] == result[k as nat],
        decreases (s_str.len() as int) - (j as int)
    {
        result.push(s_str[j as nat]);
        j = j + 1;
    }
    result.push('
');

    result
}
// </vc-code>


}

fn main() {}