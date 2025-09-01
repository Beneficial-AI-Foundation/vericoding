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
proof fn lemma_number_to_char_zero() 
ensures(number_to_char(0) == seq![]);
[proof](proof))

proof fn lemma_number_to_char_nonzero(n: nat) 
requires n > 0,
ensures(number_to_char(n) == number_to_char(n / 10).add(seq![single_digit_number_to_char(n % 10)])),
decreases n,
[proof](proof { })

fn single_digit_to_char(d: u8) -> (result: char)
    requires(d < 10),
    ensures(result == single_digit_number_to_char(d as nat)),
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

fn number_to_chars(n: u8) -> (result: Vec<char>)
    ensures(result@ == number_to_char(n as nat)),
    decreases(n as nat),
{
    if n == 0 {
        return Vec::new();
    }
    let rest = number_to_chars(n / 10);
    let last = single_digit_to_char(n % 10);
    let mut result = rest;
    result.push(last);

    proof {
        lemma_number_to_char_nonzero(n as nat);
        assert(result@ == number_to_char((n as nat) / 10).add(seq![single_digit_number_to_char((n as nat) % 10)]));
        assert(n as nat > 0);
        assert(number_to_char(n as nat) == number_to_char((n as nat) / 10).add(seq![single_digit_number_to_char((n as nat) % 10)]));
    }
    result
}

proof fn lemma_string_sequence_zero() 
ensures(string_sequence(0) == seq!['0']);
[proof](proof))

proof fn lemma_string_sequence_nonzero(n: nat) 
requires n > 0,
ensures(string_sequence(n) == string_sequence(n - 1).add(seq![' '].add(number_to_char(n)))),
decreases n,
[proof](proof { })
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
        return Vec::from(['0']);
    }
    let mut res: Vec<char> = Vec::from(['0']);
    let mut i: u8 = 0;
    while i < n
        invariant
            i <= n,
            res@ == string_sequence(i as nat),
    {
        i = i + 1;
        res.push(' ');
        let num_chars = number_to_chars(i);
        res.extend(&num_chars);
        proof {
            lemma_string_sequence_nonzero(i as nat);
            assert(string_sequence(i as nat) == string_sequence((i as nat) - 1).add(seq![' '].add(number_to_char(i as nat))));
            assert(res@ == string_sequence(i as nat));
        }
    }
    res
}
// </vc-code>

} // verus!
fn main() {}