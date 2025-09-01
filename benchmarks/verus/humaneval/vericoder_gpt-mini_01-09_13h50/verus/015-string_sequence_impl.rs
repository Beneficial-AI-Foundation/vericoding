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
fn single_digit_number_to_char_u8(d: u8) -> char
    requires d < 10
    ensures result == single_digit_number_to_char(d as nat)
{
    match d {
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

fn number_to_char_impl(n: u8) -> Vec<char>
    decreases n,
    ensures result@ == number_to_char(n as nat)
{
    if n == 0 {
        let v = Vec::from_seq(seq![]);
        proof {
            assert(v@ == seq![]);
            assert(number_to_char(0 as nat) == seq![]);
            assert(v@ == number_to_char(0 as nat));
        }
        v
    } else if n < 10 {
        let mut v = Vec::new();
        v.push(single_digit_number_to_char_u8(n));
        proof {
            assert(v@ == seq![single_digit_number_to_char_u8(n)]);
            assert(single_digit_number_to_char_u8(n) == single_digit_number_to_char(n as nat));
            assert(v@ == seq![single_digit_number_to_char(n as nat)]);
            assert(v@ == number_to_char(n as nat));
        }
        v
    } else {
        let mut v = number_to_char_impl(n / 10);
        let d_u8: u8 = n % 10;
        assert(d_u8 < 10);
        assert(single_digit_number_to_char_u8(d_u8) == single_digit_number_to_char((d_u8) as nat));
        v.push(single_digit_number_to_char_u8(d_u8));
        proof {
            assert(number_to_char(n as nat) == number_to_char((n / 10) as nat).add(seq![single_digit_number_to_char((n % 10) as nat)]));
            assert(v@ == number_to_char(n as nat));
        }
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
    let mut v: Vec<char> = Vec::new();
    v.push('0');

    let mut i: u8 = 1;
    while i <= n
        invariant v@ == string_sequence((i - 1) as nat)
        invariant (i as nat) >= 1
        invariant (i as nat) <= (n as nat + 1)
        decreases (n as nat + 1) - (i as nat)
    {
        let mut digits = number_to_char_impl(i);
        assert(digits@ == number_to_char(i as nat));

        v.push(' ');
        assert(v@ == string_sequence((i - 1) as nat).add(seq![' ']));

        v.append(&mut digits);
        proof {
            assert(v@ == string_sequence((i - 1) as nat).add(seq![' ']).add(number_to_char(i as nat)));
            assert(string_sequence(i as nat) == string_sequence((i - 1) as nat).add(seq![' '].add(number_to_char(i as nat))));
            assert(v@ == string_sequence(i as nat));
        }
        i = i + 1;
    }

    v
}
// </vc-code>

} // verus!
fn main() {}