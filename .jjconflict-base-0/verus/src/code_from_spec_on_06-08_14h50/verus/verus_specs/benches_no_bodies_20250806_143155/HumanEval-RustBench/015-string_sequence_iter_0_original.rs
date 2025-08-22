
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

proof fn sanity_check() {
    // impl-start
    assert(string_sequence(1) == seq!['0', ' ', '1']) by (compute);
    assert(string_sequence(3) == seq!['0', ' ', '1', ' ', '2', ' ', '3']) by (compute);
    assert(string_sequence(12) == seq![
        '0',
        ' ',
        '1',
        ' ',
        '2',
        ' ',
        '3',
        ' ',
        '4',
        ' ',
        '5',
        ' ',
        '6',
        ' ',
        '7',
        ' ',
        '8',
        ' ',
        '9',
        ' ',
        '1',
        '0',
        ' ',
        '1',
        '1',
        ' ',
        '1',
        '2',
    ]) by (compute);
    assert((number_to_char(158) == seq!['1', '5', '8'])) by (compute);
    // impl-end
}
// pure-end

fn single_digit_number_to_char_impl(n: u8) -> (output: char)
    // pre-conditions-start
    requires
        0 <= n <= 9,
    // pre-conditions-end
    // post-conditions-start
    ensures
        single_digit_number_to_char(n as nat) == output,
    // post-conditions-end
{
    assume(false);  // TODO: Replace with appropriate return value of type char
}

fn number_to_char_impl(n: u8) -> (char_vec: Vec<char>)
    // post-conditions-start
    ensures
        char_vec@ == number_to_char(n as nat),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn string_sequence_impl(n: u8) -> (string_seq: Vec<char>)
    // post-conditions-start
    ensures
        string_seq@ == string_sequence(n as nat),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!
fn main() {}
