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
spec fn number_to_char_u8(n: u8) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        number_to_char_u8((n / 10) as u8).add(seq![single_digit_number_to_char((n % 10) as nat)])
    }
}

spec fn string_sequence_u8(n: u8) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        string_sequence_u8((n - 1) as u8).add(seq![' '].add(number_to_char_u8(n)))
    }
}

proof fn number_to_char_u8_eq(n: u8)
    ensures
        number_to_char_u8(n) == number_to_char(n as nat),
    decreases n
{
    if n == 0 {
        // both are seq![]
    } else {
        number_to_char_u8_eq((n / 10) as u8);
        // unfold definitions
        assert(number_to_char_u8(n) == number_to_char_u8((n / 10) as u8).add(seq![single_digit_number_to_char((n % 10) as nat)]));
        assert(number_to_char(n as nat) == number_to_char((n / 10) as nat).add(seq![single_digit_number_to_char((n % 10) as nat)]));
        // use inductive hypothesis
        assert(number_to_char_u8((n / 10) as u8) == number_to_char((n / 10) as nat));
        //
        assert(number_to_char_u8(n) == number_to_char(n as nat));
    }
}

proof fn string_sequence_u8_eq(n: u8)
    ensures
        string_sequence_u8(n) == string_sequence(n as nat),
    decreases n
{
    if n == 0 {
        // both are seq!['0']
    } else {
        string_sequence_u8_eq((n - 1) as u8);
        number_to_char_u8_eq(n);
        assert(string_sequence_u8(n) == string_sequence_u8((n - 1) as u8).add(seq![' '].add(number_to_char_u8(n))));
        assert(string_sequence(n as nat) == string_sequence((n - 1) as nat).add(seq![' '].add(number_to_char(n as nat))));
        assert(string_sequence_u8((n - 1) as u8) == string_sequence((n - 1) as nat));
        assert(number_to_char_u8(n) == number_to_char(n as nat));
        assert(string_sequence_u8(n) == string_sequence(n as nat));
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
    let s = string_sequence_u8(n);
    let mut res: Vec<char> = Vec::new();
    let mut i: nat = 0;
    while i < s.len() {
        invariant(i <= s.len());
        invariant(res@ == s.slice(0, i));
        decreases (s.len() - i);
        {
            res.push(s@[i]);
            i = i + 1;
        }
    }
    proof {
        assert(!(i < s.len()));
        assert(i <= s.len());
        assert(i == s.len());
        assert(res@ == s.slice(0, i));
        assert(res@ == s);
        string_sequence_u8_eq(n);
        assert(res@ == string_sequence(n as nat));
    }
    res
}
// </vc-code>

} // verus!
fn main() {}