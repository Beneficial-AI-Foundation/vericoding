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
fn single_digit_number_to_char_exec(n: u32) -> (result: char)
    requires
        n < 10,
    ensures
        result == single_digit_number_to_char(n as nat)
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

fn number_to_vec(n: u32) -> (result: Vec<char>)
    decreases n,
    ensures
        result@ == number_to_char(n as nat)
{
    if n == 0 {
        Vec::new()
    } else {
        let mut res = number_to_vec(n / 10);
        let digit = single_digit_number_to_char_exec(n % 10);
        res.push(digit);
        res
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
    let mut i: u32 = 1;
    while i <= (n as u32)
        invariant
            1 <= i <= (n as u32) + 1,
            v@ == string_sequence((i - 1) as nat),
    {
        let v_after_zero = v@;

        v.push(' ');
        assert(v@ == v_after_zero.add(seq![' ']));

        let digits = number_to_vec(i);
        assert(digits@ == number_to_char(i as nat));

        let mut idx: usize = 0;
        while idx < digits.len()
            invariant
                0 <= idx <= digits.len(),
                v@ == string_sequence((i - 1) as nat).add(seq![' ']).add(digits@.take(idx as nat)),
        {
            v.push(digits@[@(idx as int)]);
            idx += 1;
        }
        assert(v@ == v_after_zero.add(seq![' ']).add(digits@));
        assert(v@ == string_sequence((i - 1) as nat).add(seq![' ']).add(number_to_char(i as nat)));
        assert(v@ == string_sequence(i as nat));
        proof { i += 1; }
    }
    v
}
// </vc-code>

} // verus!
fn main() {}