use vstd::prelude::*;

verus! {

spec fn single_digit_number_to_char(n: nat) -> (result:char) {
    if n == 0 {
        '0'
    } else if n == 1 {
        '1'
    } else if n == 2 {
        '2'
    } else if n == 3 {
        '3'
    } else if n == 4 {
        '4'
    } else if n == 5 {
        '5'
    } else if n == 6 {
        '6'
    } else if n == 7 {
        '7'
    } else if n == 8 {
        '8'
    } else {
        '9'
    }
}
// pure-end
// pure-end

spec fn number_to_char(n: nat) -> (result:Seq<char>)
    decreases n,
{
    if (n == 0) {
        seq![]
    } else {
        number_to_char(n / 10).add(seq![single_digit_number_to_char(n % 10)])
    }
}
// pure-end
// pure-end

spec fn string_sequence(n: nat) -> (result:Seq<char>)
    decreases n,
{
    if n == 0 {
        seq!['0']
    } else {
        string_sequence((n - 1) as nat).add(seq![' '].add(number_to_char(n)))
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_number_to_char_length(n: nat)
    ensures number_to_char(n).len() > 0
    decreases n
{
    if n > 0 {
        lemma_number_to_char_length(n / 10);
    }
}

proof fn lemma_string_sequence_length(n: nat)
    ensures string_sequence(n).len() > 0
    decreases n
{
    if n > 0 {
        lemma_string_sequence_length((n - 1) as nat);
        lemma_number_to_char_length(n);
    }
}

fn single_digit_number_to_char_impl(n: u8) -> (result: char)
    requires n <= 9
    ensures result == single_digit_number_to_char(n as nat)
{
    match n {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        _ => '9',
    }
}

fn number_to_char_impl(n: u8) -> (result: Vec<char>)
    ensures result@ == number_to_char(n as nat)
    decreases n
{
    if n == 0 {
        vec![]
    } else {
        let mut result = number_to_char_impl(n / 10);
        let digit_char = single_digit_number_to_char_impl(n % 10);
        result.push(digit_char);
        result
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def string_sequence(n: int) -> str"
docstring: |
Return a string containing space-delimited numbers starting from 0 upto n inclusive.
test_cases:
- input: 0
expected_output: "0"
- input: 5
expected_output: "0 1 2 3 4 5"
*/
// </vc-description>

// <vc-spec>
fn string_sequence_impl(n: u8) -> (string_seq: Vec<char>)
    // post-conditions-start
    ensures
        string_seq@ == string_sequence(n as nat),
    // post-conditions-end
// </vc-spec>

// <vc-code>
/* code modified by LLM (iteration 5): added decreases clause to fix recursive function error */
fn string_sequence_impl(n: u8) -> (string_seq: Vec<char>)
    ensures
        string_seq@ == string_sequence(n as nat),
    decreases n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = string_sequence_impl((n - 1) as u8);
        result.push(' ');
        let number_chars = number_to_char_impl(n);
        for i in 0..number_chars.len()
            invariant
                result@.add(number_chars@.subrange(0, i as int)) == string_sequence((n - 1) as nat).add(seq![' ']).add(number_chars@.subrange(0, i as int))
        {
            result.push(number_chars[i]);
        }
        proof {
            assert(number_chars@.subrange(0, number_chars@.len() as int) == number_chars@);
            assert(result@ == string_sequence((n - 1) as nat).add(seq![' ']).add(number_to_char(n as nat)));
            assert(result@ == string_sequence(n as nat));
        }
        result
    }
}
// </vc-code>

} // verus!
fn main() {}