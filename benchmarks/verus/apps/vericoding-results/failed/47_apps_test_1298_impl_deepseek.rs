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

proof fn count_char_decreases_lemma(ss: Seq<char>, c: char, i: int)
    requires
        i >= 0,
        i < ss.len(),
    ensures
        (ss.subrange(i, ss.len())).len() < ss.len(),
{
}

proof fn binary_string_count(s: Seq<char>)
    requires
        is_binary_string(s),
    ensures
        count_char(s, '0') + count_char(s, '1') == s.len(),
{
    if s.len() > 0 {
        binary_string_count(s.subrange(1, s.len()));
    }
}

proof fn abs_diff_count_nonnegative(s: Seq<char>)
    requires
        is_binary_string(s),
    ensures
        abs_diff_count(s) >= 0,
{
    binary_string_count(s);
}

proof fn int_to_string_valid(n: int)
    requires
        n >= 0,
    ensures
        is_valid_integer(int_to_string(n)),
{
    if n > 0 {
        int_to_string_valid(n / 10);
    }
}

proof fn string_to_int_positive(s: Seq<char>)
    requires
        is_valid_integer(s),
    ensures
        string_to_int(s) >= 0,
{
    if s.len() > 1 {
        string_to_int_positive(s.subrange(0, s.len() - 1));
    }
}

/* helper modified by LLM (iteration 5): Replaced find_char with one that handles the case when char not found within range */
fn find_char(v: &Vec<char>, start: usize, c: char) -> (result: usize)
    requires
        start < v@.len(),
        exists|i: int| start <= i < v@.len() && v@[i] == c,
    ensures
        start <= result < v@.len(),
        v@[result] == c,
        forall|j: int| start <= j < result ==> v@[j] != c,
{
    let mut i: usize = start;
    while i < v.len() && v[i] != c
        invariant
            i >= start,
            i <= v@.len(),
            forall|j: int| start <= j < i ==> v@[j] != c,
        decreases v@.len() - i
    {
        i += 1;
    }
    assert(i < v.len());
    i
}

fn seq_to_vec(s: Seq<char>) -> (result: Vec<char>)
    requires(true);
    ensures(result@ == s);
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@ == s.subrange(0, i),
        decreases s.len() - i
    {
        v.push(s[i as usize]);
        i += 1;
    }
    v
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
    /* code modified by LLM (iteration 5): Fixed variable name and ensured binary_end is within bounds */
    let newline_pos = find_char(&stdin_input, 0, '\n');
    assert(newline_pos < stdin_input@.len() - 1);
    
    let binary_end = find_char(&stdin_input, newline_pos + 1, '\n');
    let binary_part = stdin_input.subrange(newline_pos + 1, binary_end);
    
    proof {
        binary_string_count(binary_part@);
        abs_diff_count_nonnegative(binary_part@);
        int_to_string_valid(abs_diff_count(binary_part@));
    }
    
    let abs_diff = abs_diff_count(binary_part@);
    let result_num = int_to_string(abs_diff);
    let mut result_vec = seq_to_vec(result_num);
    result_vec.push('\n');
    result_vec
}
// </vc-code>


}
fn main() {}