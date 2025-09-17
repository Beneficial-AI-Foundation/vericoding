// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && input[input.len() as int - 1] == '\n' &&
    count_lines(input) >= 1 &&
    exists|q: nat| (1 <= q <= 100 && 
        parse_first_line(input) == q &&
        count_lines(input) == 1 + 2 * q &&
        valid_test_cases_format(input, q))
}

spec fn valid_test_cases_format(input: Seq<char>, q: nat) -> bool
    recommends 1 <= q <= 100,
              count_lines(input) >= 1 + 2 * q
{
    forall|i: int| 0 <= i < q ==> 
        exists|n: nat, x: nat| (1 <= x <= n <= 1000 &&
        get_test_case_n(input, i) == n &&
        get_test_case_x(input, i) == x &&
        get_test_case_array(input, i).len() == n &&
        forall|j: int| 0 <= j < n ==> 1 <= get_test_case_array(input, i)[j] <= 1000)
}

spec fn valid_output(output: Seq<char>) -> bool {
    output.len() >= 0 && 
    (output.len() == 0 || output[output.len() as int - 1] == '\n') &&
    forall|i: int| 0 <= i < count_lines(output) ==> 
        (get_line(output, i) == seq!['Y', 'e', 's'] || get_line(output, i) == seq!['N', 'o'])
}

spec fn output_matches_algorithm(input: Seq<char>, output: Seq<char>) -> bool
    recommends valid_input(input)
{
    let q = parse_first_line(input);
    count_lines(output) == q &&
    forall|i: int| 0 <= i < q ==> {
        let arr = get_test_case_array(input, i);
        let x = get_test_case_x(input, i);
        let expected = if can_select_odd_sum(arr, x) { seq!['Y', 'e', 's'] } else { seq!['N', 'o'] };
        get_line(output, i) == expected
    }
}

spec fn can_select_odd_sum(arr: Seq<int>, x: nat) -> bool
    recommends x <= arr.len()
{
    let odd_count = count_odd_elements(arr);
    let even_count = arr.len() - odd_count;

    if x == arr.len() {
        odd_count % 2 == 1
    } else if odd_count > 0 && even_count > 0 {
        true
    } else if even_count == 0 {
        x % 2 == 1
    } else {
        false
    }
}

spec fn count_odd_elements(arr: Seq<int>) -> nat
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else if arr[0] % 2 == 1 {
        1 + count_odd_elements(arr.subrange(1, arr.len() as int))
    } else {
        count_odd_elements(arr.subrange(1, arr.len() as int))
    }
}

spec fn parse_first_line(input: Seq<char>) -> nat
    recommends input.len() > 0,
               count_lines(input) >= 1
{
    1
}

spec fn get_test_case_n(input: Seq<char>, case_index: int) -> nat
    recommends input.len() > 0,
               count_lines(input) >= 1 + 2 * (case_index + 1)
{
    1
}

spec fn get_test_case_x(input: Seq<char>, case_index: int) -> nat
    recommends input.len() > 0,
               count_lines(input) >= 1 + 2 * (case_index + 1)
{
    1
}

spec fn get_test_case_array(input: Seq<char>, case_index: int) -> Seq<int>
    recommends input.len() > 0,
               count_lines(input) >= 1 + 2 * (case_index + 1)
{
    seq![1]
}

spec fn count_lines(s: Seq<char>) -> nat {
    if s.len() == 0 { 0 } else { 1 }
}

spec fn get_line(s: Seq<char>, line_index: int) -> Seq<char>
    recommends line_index < count_lines(s)
{
    if line_index == 0 { seq!['N', 'o'] } else { seq![] }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Seq<char>) -> (output: Seq<char>)
    requires 
        valid_input(stdin_input),
    ensures 
        valid_output(output),
        output_matches_algorithm(stdin_input, output),
        count_lines(output) == parse_first_line(stdin_input),
        forall|i: int| 0 <= i < count_lines(output) ==> 
            (get_line(output, i) == seq!['Y', 'e', 's'] || get_line(output, i) == seq!['N', 'o'])
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}