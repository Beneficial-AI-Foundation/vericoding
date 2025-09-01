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
proof fn number_to_char_recursive_property(n: nat)
    decreases n
{
    if n == 0 {
    } else {
        number_to_char_recursive_property(n / 10);
    }
}

proof fn string_sequence_recursive_property(n: nat)
    decreases n
{
    if n == 0 {
    } else {
        number_to_char_recursive_property(n);
        string_sequence_recursive_property((n - 1) as nat);
    }
}

fn single_digit_number_to_char_impl(n: u8) -> (c: char)
    requires
        n < 10,
    ensures
        c == single_digit_number_to_char(n as nat),
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

fn number_to_char_impl(n: u8) -> (v: Vec<char>)
    decreases n
    ensures
        v@ == number_to_char(n as nat),
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
        let mut v = string_sequence_impl(n - 1);
        v.push(' ');
        let mut num_chars = number_to_char_impl(n);
        v.append(&mut num_chars);
        v
    }
}
// </vc-code>

} // verus!
fn main() {}