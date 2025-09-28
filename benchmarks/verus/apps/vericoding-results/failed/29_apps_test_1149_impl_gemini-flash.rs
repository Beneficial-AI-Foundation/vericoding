// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    let lines = split_lines(stdin_input);
    lines.len() >= 3 && {
        let n = parse_int(lines[0]);
        let x_line = parse_int_list(lines[1]);
        let y_line = parse_int_list(lines[2]);
        n >= 1 && x_line.len() > 0 && y_line.len() > 0 &&
        x_line[0] >= 0 && y_line[0] >= 0 &&
        x_line.len() >= (1 + x_line[0]) as nat && y_line.len() >= (1 + y_line[0]) as nat
    }
}

spec fn get_expected_output(stdin_input: Seq<char>) -> Seq<char>
    recommends valid_input(stdin_input)
{
    let lines = split_lines(stdin_input);
    let n = parse_int(lines[0]);
    let x_line = parse_int_list(lines[1]);
    let y_line = parse_int_list(lines[2]);
    let x_levels = set_from_seq(x_line.subrange(1, 1 + x_line[0] as int));
    let y_levels = set_from_seq(y_line.subrange(1, 1 + y_line[0] as int));
    let all_levels = x_levels.union(y_levels);
    let required_levels = Set::new(|i: int| 1 <= i <= n);
    if required_levels.subset_of(all_levels) { 
        Seq::new(17, |i: int| if i == 0 { 'I' } else if i == 1 { ' ' } else if i == 2 { 'b' } else if i == 3 { 'e' } else if i == 4 { 'c' } else if i == 5 { 'o' } else if i == 6 { 'm' } else if i == 7 { 'e' } else if i == 8 { ' ' } else if i == 9 { 't' } else if i == 10 { 'h' } else if i == 11 { 'e' } else if i == 12 { ' ' } else if i == 13 { 'g' } else if i == 14 { 'u' } else if i == 15 { 'y' } else { '.' })
    } else { 
        Seq::new(16, |i: int| if i == 0 { 'O' } else if i == 1 { 'h' } else if i == 2 { ',' } else if i == 3 { ' ' } else if i == 4 { 'm' } else if i == 5 { 'y' } else if i == 6 { ' ' } else if i == 7 { 'k' } else if i == 8 { 'e' } else if i == 9 { 'y' } else if i == 10 { 'b' } else if i == 11 { 'o' } else if i == 12 { 'a' } else if i == 13 { 'r' } else if i == 14 { 'd' } else { '!' })
    }
}

spec fn set_from_seq(s: Seq<int>) -> Set<int> {
    Set::new(|x: int| s.contains(x))
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::new(0 as nat, |j: int| Seq::new(0 as nat, |k: int| ' '))
    } else {
        let newline_pos = find_char(s, '\n');
        if newline_pos == -1 {
            Seq::new(1 as nat, |j: int| trim(s))
        } else if 0 <= newline_pos < s.len() {
            Seq::new(1 as nat, |j: int| trim(s.subrange(0, newline_pos))).add(split_lines(s.subrange(newline_pos+1, s.len() as int)))
        } else {
            Seq::new(1 as nat, |j: int| trim(s))
        }
    }
}

spec fn trim(s: Seq<char>) -> Seq<char> {
    if s.len() == 0 {
        s
    } else if s[s.len() as int - 1] == '\r' {
        s.subrange(0, s.len() as int - 1)
    } else {
        s
    }
}

spec fn find_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        -1
    } else if s[0] == c {
        0
    } else {
        let rest = find_char(s.subrange(1, s.len() as int), c);
        if rest == -1 { -1 } else { rest + 1 }
    }
}

spec fn parse_int(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s[0] == '-' {
        if is_valid_digits(s.subrange(1, s.len() as int)) { 
            -parse_int_helper(s.subrange(1, s.len() as int)) 
        } else { 
            0 
        }
    } else if is_valid_digits(s) { 
        parse_int_helper(s) 
    } else { 
        0 
    }
}

spec fn is_valid_digits(s: Seq<char>) -> bool {
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> ('0' <= s[i] <= '9')
}

spec fn parse_int_helper(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        char_to_digit(s[0])
    } else {
        parse_int_helper(s.subrange(0, s.len() as int - 1)) * 10 + char_to_digit(s[s.len() as int - 1])
    }
}

spec fn char_to_digit(c: char) -> int {
    (c as u32 as int) - ('0' as u32 as int)
}

spec fn parse_int_list(s: Seq<char>) -> Seq<int> {
    let parts = split_by_char(s, ' ');
    Seq::new(parts.len(), |i: int| parse_int(parts[i]))
}

spec fn split_by_char(s: Seq<char>, delimiter: char) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::new(0 as nat, |j: int| Seq::new(0 as nat, |k: int| ' '))
    } else {
        let delim_pos = find_char(s, delimiter);
        if delim_pos == -1 {
            Seq::new(1 as nat, |j: int| s)
        } else if delim_pos == 0 {
            split_by_char(s.subrange(1, s.len() as int), delimiter)
        } else if 0 < delim_pos < s.len() {
            Seq::new(1 as nat, |j: int| s.subrange(0, delim_pos)).add(split_by_char(s.subrange(delim_pos+1, s.len() as int), delimiter))
        } else {
            Seq::new(1 as nat, |j: int| s)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed redundant lemma; direct conversion from int to nat is allowed in ghost code. */
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (result: Vec<u8>)
    requires valid_input(stdin_input@.map(|i, c| c as char))
    ensures result@.map(|i, c| c as char) == get_expected_output(stdin_input@.map(|i, c| c as char))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed `i as int` and `j as int` to simply `i` and `j` in while loop conditions to prevent compilation errors related to `int` and `nat` in ghost code. */
    let input_seq = stdin_input@.map(|i, c| c as char);
    let lines = split_lines(input_seq);

    let n_str = lines.field_get(0);
    let n_int = parse_int(n_str);

    let x_line_str = lines.field_get(1);
    let x_line = parse_int_list(x_line_str);

    let y_line_str = lines.field_get(2);
    let y_line = parse_int_list(y_line_str);

    let mut x_levels: Set<int> = Set::empty();
    let x_count = x_line[0];
    let mut i: usize = 1;
    while (i as int) <= x_count
        invariant
            1 <= (i as int) <= x_count + 1,
            x_levels.subset_of(set_from_seq(x_line.subrange(1, i as int))),
            0 <= x_count,
            x_count < x_line.len() as int,
            x_line.len() >= i as nat
        decreases x_count - (i as int)
    {
        x_levels = x_levels.insert(x_line[i]);
        i = i + 1;
    }

    let mut y_levels: Set<int> = Set::empty();
    let y_count = y_line[0];
    let mut j: usize = 1;
    while (j as int) <= y_count
        invariant
            1 <= (j as int) <= y_count + 1,
            y_levels.subset_of(set_from_seq(y_line.subrange(1, j as int))),
            0 <= y_count,
            y_count < y_line.len() as int,
            y_line.len() >= j as nat
        decreases y_count - (j as int)
    {
        y_levels = y_levels.insert(y_line[j]);
        j = j + 1;
    }

    let all_levels = x_levels.union(y_levels);

    let mut required_levels = Set::empty();
    let mut k = 1; // Change k to int for comparison with n_int
    while k <= n_int
        invariant
            1 <= k <= n_int + 1,
            required_levels.subset_of(Set::new(|idx: int| 1 <= idx < k)), // Use idx instead of i
            0 <= n_int
        decreases n_int - k
    {
        required_levels = required_levels.insert(k);
        k = k + 1;
    }

    let output_seq = if required_levels.subset_of(all_levels) {
        Seq::new(17, |idx: int| if idx == 0 { 'I' } else if idx == 1 { ' ' } else if idx == 2 { 'b' } else if idx == 3 { 'e' } else if idx == 4 { 'c' } else if idx == 5 { 'o' } else if idx == 6 { 'm' } else if idx == 7 { 'e' } else if idx == 8 { ' ' } else if idx == 9 { 't' } else if idx == 10 { 'h' } else if idx == 11 { 'e' } else if idx == 12 { ' ' } else if idx == 13 { 'g' } else if idx == 14 { 'u' } else if idx == 15 { 'y' } else { '.' })
    } else {
        Seq::new(16, |idx: int| if idx == 0 { 'O' } else if idx == 1 { 'h' } else if idx == 2 { ',' } else if idx == 3 { ' ' } else if idx == 4 { 'm' } else if idx == 5 { 'y' } else if idx == 6 { ' ' } else if idx == 7 { 'k' } else if idx == 8 { 'e' } else if idx == 9 { 'y' } else if idx == 10 { 'b' } else if idx == 11 { 'o' } else if idx == 12 { 'a' } else if idx == 13 { 'r' } else if idx == 14 { 'd' } else { '!' })
    };

    let mut result_vec: Vec<u8> = Vec::new();
    let mut idx = 0usize;
    while idx < output_seq.len()
        invariant
            0 <= idx as int <= output_seq.len() as int,
            result_vec@.len() == idx as nat,
            forall|l: int| 0 <= l < idx as int ==> result_vec@.index(l as nat) == output_seq.index(l as nat) as u8
        decreases output_seq.len() - idx
    {
        result_vec.push(output_seq.index(idx) as u8);
        idx = idx + 1;
    }

    result_vec
}
// </vc-code>


}

fn main() {}