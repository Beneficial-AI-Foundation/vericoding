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
proof fn lemma_number_to_char_positive(n: nat)
    requires n > 0
    ensures number_to_char(n).len() > 0
    decreases n
{
    if n < 10 {
        assert(number_to_char(n) == seq![single_digit_number_to_char(n % 10)]);
    } else {
        lemma_number_to_char_positive(n / 10);
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

fn extend_vec_with_seq(vec: &mut Vec<char>, seq: Vec<char>)
    ensures vec@ == old(vec)@ + seq@
{
    let mut i = 0;
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            vec@ == old(vec)@ + seq@.subrange(0, i as int)
    {
        vec.push(seq[i]);
        i += 1;
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
        let number_chars = number_to_char_impl(n);
        extend_vec_with_seq(&mut result, number_chars);
        result
    }
}
// </vc-code>

} // verus!
fn main() {}