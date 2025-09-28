// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else if n == 2 { seq!['2'] }
    else if n == 3 { seq!['3'] }
    else if n == 4 { seq!['4'] }
    else if n == 5 { seq!['5'] }
    else if n == 6 { seq!['6'] }
    else if n == 7 { seq!['7'] }
    else if n == 8 { seq!['8'] }
    else if n == 9 { seq!['9'] }
    else if n == 10 { seq!['1', '0'] }
    else if n == 11 { seq!['1', '1'] }
    else if n == 12 { seq!['1', '2'] }
    else if n == 13 { seq!['1', '3'] }
    else if n == 14 { seq!['1', '4'] }
    else if n == 15 { seq!['1', '5'] }
    else if n == 16 { seq!['1', '6'] }
    else if n == 17 { seq!['1', '7'] }
    else if n == 18 { seq!['1', '8'] }
    else if n == 19 { seq!['1', '9'] }
    else if n == 20 { seq!['2', '0'] }
    else if n == 21 { seq!['2', '1'] }
    else if n == 22 { seq!['2', '2'] }
    else if n == 23 { seq!['2', '3'] }
    else { seq!['0'] }
}

spec fn valid_input(input: Seq<char>) -> bool {
    exists|a: int, b: int| 0 <= a <= 23 && 0 <= b <= 23 && 
    (input == int_to_string(a) + seq![' '] + int_to_string(b) + seq!['\n'] ||
     input == int_to_string(a) + seq![' '] + int_to_string(b))
}

spec fn contest_start_time(a: int, b: int) -> int {
    (a + b) % 24
}

spec fn correct_output(input: Seq<char>, result: Seq<char>) -> bool {
    valid_input(input) ==> 
    exists|a: int, b: int| 0 <= a <= 23 && 0 <= b <= 23 && 
    (input == int_to_string(a) + seq![' '] + int_to_string(b) + seq!['\n'] ||
     input == int_to_string(a) + seq![' '] + int_to_string(b)) &&
    result == int_to_string(contest_start_time(a, b)) + seq!['\n']
}
// </vc-preamble>

// <vc-helpers>
fn exec_int_to_string(n: u8) -> (s: String)
    requires 0 <= n <= 23,
    ensures s@ == int_to_string(n as int),
{
    if n == 0 { "0".to_string() }
    else if n == 1 { "1".to_string() }
    else if n == 2 { "2".to_string() }
    else if n == 3 { "3".to_string() }
    else if n == 4 { "4".to_string() }
    else if n == 5 { "5".to_string() }
    else if n == 6 { "6".to_string() }
    else if n == 7 { "7".to_string() }
    else if n == 8 { "8".to_string() }
    else if n == 9 { "9".to_string() }
    else if n == 10 { "10".to_string() }
    else if n == 11 { "11".to_string() }
    else if n == 12 { "12".to_string() }
    else if n == 13 { "13".to_string() }
    else if n == 14 { "14".to_string() }
    else if n == 15 { "15".to_string() }
    else if n == 16 { "16".to_string() }
    else if n == 17 { "17".to_string() }
    else if n == 18 { "18".to_string() }
    else if n == 19 { "19".to_string() }
    else if n == 20 { "20".to_string() }
    else if n == 21 { "21".to_string() }
    else if n == 22 { "22".to_string() }
    else { "23".to_string() }
}

/* helper modified by LLM (iteration 5): fixed compilation error by using Vec::from_seq */
fn parse_nat_optional(s_vec: &Vec<char>) -> (res: Option<u8>)
    ensures
        res.is_some() ==> (exists|i: int| 0 <= i <= 23 && s_vec@ == int_to_string(i) && res.unwrap() as int == i),
        res.is_none() ==> (forall|i: int| 0 <= i <= 23 ==> s_vec@ != int_to_string(i)),
{
    let mut i: u8 = 0;
    while i <= 23
        invariant
            0 <= i <= 24,
            forall|j: int| 0 <= j < i ==> s_vec@ != int_to_string(j),
        decreases 23 - i,
    {
        let i_str = exec_int_to_string(i);
        let i_str_vec = Vec::from_seq(i_str.view());
        if s_vec.as_slice() == i_str_vec.as_slice() {
             return Some(i);
        }
        i = i + 1;
    }
    None
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    ensures correct_output(input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using Vec::from_seq */
    let v = Vec::from_seq(input.view());

    let mut space_idx: usize = 0;
    while space_idx < v.len() && v[space_idx] != ' '
        invariant
            0 <= space_idx <= v.len(),
            forall|i: int| 0 <= i < space_idx ==> v@[i] != ' ',
        decreases v.len() - space_idx,
    {
        space_idx += 1;
    }

    if space_idx == v.len() {
        // This case is not covered by the spec, but we should handle it gracefully.
        // The spec implies valid_input, which requires a space.
        // Returning a default valid output for an unspecified case.
        return "0\n".to_string();
    }

    let a_str_vec = (&v[0..space_idx]).to_vec();

    let mut end_idx = space_idx + 1;
    while end_idx < v.len() && v[end_idx] != '\n'
        invariant
            space_idx < end_idx <= v.len(),
            forall|i: int| space_idx < i < end_idx ==> v@[i] != '\n',
        decreases v.len() - end_idx,
    {
        end_idx += 1;
    }

    let b_str_vec = (&v[space_idx + 1..end_idx]).to_vec();

    let res_a = parse_nat_optional(&a_str_vec);
    let res_b = parse_nat_optional(&b_str_vec);

    if res_a.is_none() || res_b.is_none() {
        // Also not covered by spec, handle gracefully.
        return "0\n".to_string();
    }

    let a = res_a.unwrap();
    let b = res_b.unwrap();

    let result_val = (a + b) % 24;

    let result_str = exec_int_to_string(result_val);
    result_str + "\n"
}
// </vc-code>


}

fn main() {}