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
fn single_digit_number_to_char_impl(n: u8) -> (result: char)
    requires n < 10,
    ensures result == single_digit_number_to_char(n as nat),
{
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

fn number_to_char_impl(n: u8) -> (result: Vec<char>)
    ensures result@ == number_to_char(n as nat),
    decreases n,
{
    if n == 0 {
        vec![]
    } else {
        let mut v = number_to_char_impl(n / 10);
        v.push(single_digit_number_to_char_impl(n % 10));
        v
    }
}
// </vc-helpers>

// <vc-spec>
fn string_sequence_impl(n: u8) -> (string_seq: Vec<char>)
    // post-conditions-start
    ensures
        string_seq@ == string_sequence(n as nat),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = string_sequence_impl((n - 1) as u8);
        result.push(' ');
        let num_chars = number_to_char_impl(n);
        let mut i: usize = 0;
        while i < num_chars.len()
            invariant
                0 <= i <= num_chars.len(),
                result@ == string_sequence((n - 1) as nat).add(seq![' ']).add(num_chars@.subrange(0, i as int)),
                num_chars@ == number_to_char(n as nat),
            decreases num_chars.len() - i,
        {
            result.push(num_chars[i]);
            i = i + 1;
        }
        result
    }
}
// </vc-code>

} // verus!
fn main() {}