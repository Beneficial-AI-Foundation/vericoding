// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i] == '0' || #[trigger] s[i] == '1')
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && (s[0] != '0' || s.len() == 1) && forall|i: int| 0 <= i < s.len() ==> ('0' <= #[trigger] s[i] <= '9')
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else { (if s[0] == c { 1int } else { 0int }) + count_char(s.subrange(1, s.len() as int), c) }
}

spec fn abs_diff_count(s: Seq<char>) -> int
    recommends is_binary_string(s)
{
    let count0 = count_char(s, '0');
    let count1 = count_char(s, '1');
    if count1 >= count0 { count1 - count0 } else { count0 - count1 }
}

spec fn int_to_string(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n == 0 { seq!['0'] }
    else if n < 10 { seq![char_of_digit(n)] }
    else { int_to_string(n / 10).add(seq![char_of_digit(n % 10)]) }
}

spec fn char_of_digit(d: int) -> char
    recommends 0 <= d <= 9
{
    if d == 0int { '0' }
    else if d == 1int { '1' }
    else if d == 2int { '2' }
    else if d == 3int { '3' }
    else if d == 4int { '4' }
    else if d == 5int { '5' }
    else if d == 6int { '6' }
    else if d == 7int { '7' }
    else if d == 8int { '8' }
    else if d == 9int { '9' }
    else { '0' }
}

spec fn string_to_int(s: Seq<char>) -> int
    recommends is_valid_integer(s)
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else if s.len() == 1 { (s[0] as int) - ('0' as int) }
    else { string_to_int(s.subrange(0, s.len() - 1)) * 10int + ((s[s.len() - 1] as int) - ('0' as int)) }
}
// </vc-preamble>

// <vc-helpers>
fn find_char_exec(v: &Vec<char>, start: usize, target: char) -> (pos: usize)
    requires
        start <= v.len(),
    ensures
        start <= pos && pos <= v.len(),
        (pos < v.len()) ==> (v@.index(pos as int) == target),
        forall|i: int| start <= i < pos ==> v@.index(i) != target,
{
    let mut i = start;
    while i < v.len()
        invariant
            start <= i <= v.len(),
            forall|j: int| start <= j < i ==> v@.index(j) != target,
    {
        if v[i] == target {
            return i;
        }
        i = i + 1;
    }
    i
}

/* helper modified by LLM (iteration 5): fixed type error in subrange call */
#[verifier::spinoff_prover]
proof fn lemma_count_char_add(s1: Seq<char>, s2: Seq<char>, c: char)
    ensures
        count_char(s1.add(s2), c) == count_char(s1, c) + count_char(s2, c),
    decreases s1.len(),
{
    if s1.len() > 0 {
        lemma_count_char_add(s1.subrange(1, s1.len() as int), s2, c);
    }
}

fn count_zeros_and_ones_exec(s: &[char]) -> (res: (u64, u64))
    requires
        is_binary_string(s@),
    ensures
        res.0 as int == count_char(s@, '0'),
        res.1 as int == count_char(s@, '1'),
{
    let mut count0: u64 = 0;
    let mut count1: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_binary_string(s@),
            count0 as int == count_char(s@.subrange(0, i as int), '0'),
            count1 as int == count_char(s@.subrange(0, i as int), '1'),
        decreases s.len() - i,
    {
        proof {
            let sub = s@.subrange(0, i as int);
            let next_sub = s@.subrange(0, (i + 1) as int);
            let added_char_seq = s@.subrange(i as int, (i + 1) as int);
            assert(next_sub == sub.add(added_char_seq));
            lemma_count_char_add(sub, added_char_seq, '0');
            lemma_count_char_add(sub, added_char_seq, '1');
        }
        if s[i] == '0' {
            count0 = count0 + 1;
        } else {
            count1 = count1 + 1;
        }
        i = i + 1;
    }
    (count0, count1)
}

fn char_of_digit_exec(d: u8) -> (c: char)
    requires
        d <= 9,
    ensures
        c == char_of_digit(d as int),
{
    let c =
        if d == 0 { '0' } else if d == 1 { '1' } else if d == 2 { '2' }
        else if d == 3 { '3' } else if d == 4 { '4' } else if d == 5 { '5' }
        else if d == 6 { '6' } else if d == 7 { '7' } else if d == 8 { '8' }
        else { '9' };
    proof {
        reveal_with_fuel(char_of_digit, 11);
    }
    c
}

fn int_to_string_rec_exec(n: u64) -> (res: Vec<char>)
    requires
        n > 0,
    ensures
        res@ == int_to_string(n as int),
    decreases n,
{
    if n < 10 {
        let d = n as u8;
        let c = char_of_digit_exec(d);
        proof {
            reveal_with_fuel(int_to_string, 2);
        }
        vec![c]
    } else {
        let mut v = int_to_string_rec_exec(n / 10);
        let last_digit = (n % 10) as u8;
        let c = char_of_digit_exec(last_digit);
        proof {
            reveal_with_fuel(int_to_string, 2);
        }
        v.push(c);
        v
    }
}

fn int_to_string_exec(n: u64) -> (res: Vec<char>)
    requires
        n >= 0,
    ensures
        res@ == int_to_string(n as int),
{
    if n == 0 {
        proof {
            reveal_with_fuel(int_to_string, 2);
        }
        vec!['0']
    } else {
        int_to_string_rec_exec(n)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires 
        stdin_input@.len() > 0,
        exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n',
        exists|newline_pos: int| {
            0 <= newline_pos < stdin_input@.len() && stdin_input@[newline_pos] == '\n' &&
            newline_pos + 1 < stdin_input@.len() &&
            exists|binary_end: int| {
                newline_pos + 1 <= binary_end <= stdin_input@.len() &&
                (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
                is_valid_integer(stdin_input@.subrange(0, newline_pos)) &&
                is_binary_string(stdin_input@.subrange(newline_pos + 1, binary_end))
            }
        },
    ensures 
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        exists|newline_pos: int| {
            0 <= newline_pos < stdin_input@.len() && stdin_input@[newline_pos] == '\n' &&
            newline_pos + 1 < stdin_input@.len() &&
            exists|binary_end: int| {
                newline_pos + 1 <= binary_end <= stdin_input@.len() &&
                (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
                is_binary_string(stdin_input@.subrange(newline_pos + 1, binary_end)) &&
                result@ == int_to_string(abs_diff_count(stdin_input@.subrange(newline_pos + 1, binary_end))).add(seq!['\n'])
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced subslice with slice syntax and fixed call */
    let newline_pos = find_char_exec(&stdin_input, 0, '\n');
    let binary_start = newline_pos + 1;
    let binary_end = find_char_exec(&stdin_input, binary_start, '\n');

    let binary_slice = &stdin_input[binary_start..binary_end];
    let (count0, count1) = count_zeros_and_ones_exec(binary_slice);

    let diff = if count0 > count1 {
        count0 - count1
    } else {
        count1 - count0
    };

    let mut result = int_to_string_exec(diff);
    result.push('\n');

    result
}
// </vc-code>


}
fn main() {}