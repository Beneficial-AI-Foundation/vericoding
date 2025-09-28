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
/* helper modified by LLM (iteration 5): lemma: find_char returns index i when first occurrence at i */
fn lemma_find_char_from(s: &Vec<char>, c: char, start: usize, i: usize)
    requires
        start <= i && i < s.len(),
        forall|j: int| start as int <= j && j < i as int ==> s@[j] != c,
        s@[i as int] == c,
    ensures
        find_char(s@, c, start as int) == i as int,
    decreases
        i as int - start as int
{
    if i == start {
        // by definition of find_char, if s[start] == c then find_char(s, c, start) == start
    } else {
        // s[start] != c, so find_char(s, c, start) == find_char(s, c, start+1)
        assert(s@[start as int] != c);
        lemma_find_char_from(s, c, start + 1, i);
    }
}

/* helper modified by LLM (iteration 5): lemma: find_char returns -1 when no occurrence */
fn lemma_find_char_not_found(s: &Vec<char>, c: char, start: usize)
    requires
        start <= s.len(),
        forall|j: int| start as int <= j && j < s.len() as int ==> s@[j] != c,
    ensures
        find_char(s@, c, start as int) == -1,
    decreases
        s.len() as int - start as int
{
    if start >= s.len() {
        // empty tail: find_char returns -1
    } else {
        assert(s@[start as int] != c);
        lemma_find_char_not_found(s, c, start + 1);
    }
}

/* helper modified by LLM (iteration 5): find first occurrence in Vec, returns isize (-1 if not found) */
fn find_char_vec(s: &Vec<char>, c: char, start: usize) -> (result: isize)
    requires
        start <= s.len(),
    ensures
        result as int == find_char(s@, c, start as int),
    decreases
        s.len() as int - start as int
{
    let mut i: usize = start;
    while i < s.len()
        invariant
            start <= i && i <= s.len(),
            forall|j: int| start as int <= j && j < i as int ==> s@[j] != c,
        decreases
            s.len() as int - i as int
    {
        if s[i] == c {
            proof {
                lemma_find_char_from(s, c, start, i);
            }
            return i as isize;
        }
        i += 1;
    }
    proof {
        lemma_find_char_not_found(s, c, start);
    }
    -1
}

/* helper modified by LLM (iteration 5): find last occurrence in Vec, returns isize (-1 if not found) */
fn rfind_char_vec(s: &Vec<char>, c: char) -> (result: isize)
    ensures
        result as int == rfind_char(s@, c),
    decreases
        s.len() as int
{
    let mut i: usize = 0;
    let mut last: isize = -1;
    while i < s.len()
        invariant
            -1 <= last && last < s.len() as isize,
            last as int == rfind_char(s@.subrange(0, i as int), c),
        decreases
            s.len() as int - i as int
    {
        if s[i] == c {
            last = i as isize;
        }
        i += 1;
    }
    last
}

/* helper modified by LLM (iteration 5): compute swap time using runtime Vec (returns usize) */
fn compute_swap_time_vec(s: &Vec<char>) -> (result: usize)
    requires
        valid_input(s@),
    ensures
        (result as nat) == compute_swap_time(s@),
    decreases
        s.len() as int
{
    // build reversed vector
    let mut rev: Vec<char> = Vec::new();
    let mut idx: usize = s.len();
    while idx > 0
        invariant
            0 <= idx && idx <= s.len(),
        decreases
            idx as int
    {
        idx -= 1;
        rev.push(s[idx]);
    }

    let first_f = find_char_vec(&rev, 'F', 0);
    if first_f == -1 { return 0usize; }
    assert(first_f >= 0);
    let first_m_after_f = find_char_vec(&rev, 'M', (first_f + 1) as usize);
    if first_m_after_f == -1 { return 0usize; }
    let last_m = rfind_char_vec(&rev, 'M');
    if last_m == -1 { return 0usize; }
    if last_m < first_m_after_f { return 0usize; }

    let mut balance: isize = 0;
    let mut f_count: usize = 0;
    let mut i: usize = first_m_after_f as usize;
    let last_m_usize: usize = last_m as usize;
    while i < last_m_usize + 1
        invariant
            first_m_after_f as usize <= i && i <= last_m_usize + 1,
        decreases
            (last_m_usize + 1) as int - i as int
    {
        let ch = rev[i];
        if ch == 'M' {
            balance += 1;
        } else {
            if balance > 0 { balance -= 1; }
            f_count += 1;
        }
        i += 1;
    }

    let tot: isize = balance + ((first_m_after_f as isize) - first_f - 1) + f_count as isize;
    if tot < 0 { 0usize } else { tot as usize }
}

/* helper modified by LLM (iteration 5): convert usize number to Vec<char> representing its decimal digits */
fn nat_to_string_vec(n0: usize) -> (result: Vec<char>)
    ensures
        result@ == nat_to_string(n0 as nat),
    decreases
        n0 as int
{
    if n0 == 0 {
        let mut v: Vec<char> = Vec::new();
        v.push('0');
        v
    } else {
        let mut n = n0;
        let mut acc: Vec<char> = Vec::new();
        while n > 0
            invariant
                0 <= n && n <= n0,
            decreases
                n as int
        {
            let digit = (n % 10) as u8;
            acc.push((('0' as u8) + digit) as char);
            n = n / 10;
        }
        let mut res: Vec<char> = Vec::new();
        let mut j: usize = acc.len();
        while j > 0
            invariant
                0 <= j && j <= acc.len(),
            decreases
                j as int
        {
            j -= 1;
            res.push(acc[j]);
        }
        res
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
/* code modified by LLM (iteration 5): call helpers to compute result and format with newline */
{
    let val_nat = compute_swap_time_vec(&input);
    let mut s = nat_to_string_vec(val_nat);
    s.push('\n');
    s
}

// </vc-code>


}

fn main() {}