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
proof fn lemma_number_to_char_base_case()
    ensures
        number_to_char(0) == seq![],
{
}

proof fn lemma_number_to_char_recursive(n: nat)
    requires
        n > 0,
    ensures
        number_to_char(n) == number_to_char(n / 10).add(seq![single_digit_number_to_char(n % 10)]),
{
}

proof fn lemma_string_sequence_base_case()
    ensures
        string_sequence(0) == seq!['0'],
{
}

proof fn lemma_string_sequence_recursive(n: nat)
    requires
        n > 0,
    ensures
        string_sequence(n) == string_sequence((n - 1) as nat).add(seq![' '].add(number_to_char(n))),
{
}

spec fn string_sequence_impl_ghost(n: nat) -> (result: Seq<char>)
    decreases n,
{
    if n == 0 {
        seq!['0']
    } else {
        string_sequence_impl_ghost((n - 1) as nat).add(seq![' '].add(number_to_char(n)))
    }
}

proof fn lemma_string_sequence_impl_ghost_equiv(n: nat)
    ensures
        string_sequence_impl_ghost(n) == string_sequence(n),
{
    if n > 0 {
        lemma_string_sequence_impl_ghost_equiv((n - 1) as nat);
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
    let mut string_seq = Vec::new();
    let mut i: u8 = 0;
    while i <= n
        invariant
            i <= n + 1,
            string_seq@ == string_sequence_impl_ghost((i - 1) as nat),
    {
        if i == 0 {
            string_seq.push('0');
        } else {
            string_seq.push(' ');
            
            let mut num = i;
            let mut digits = Vec::new();
            while num > 0
                invariant
                    num <= i,
                    digits@.len() == number_to_char(num as nat)@.len(),
                    digits@ == number_to_char(num as nat)@,
            {
                let digit_char = match num % 10 {
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
                };
                digits.push(digit_char);
                num = num / 10;
            }
            
            if digits.is_empty() {
                digits.push('0');
            }
            
            let mut j = digits.len();
            while j > 0
                invariant
                    j <= digits@.len(),
                    string_seq@.len() == old(string_seq)@.len() + (digits@.len() - j),
                    string_seq@ == old(string_seq)@ + digits@.subrange(j, digits@.len()),
            {
                j = j - 1;
                string_seq.push(digits[j]);
            }
        }
        i = i + 1;
    }
    lemma_string_sequence_impl_ghost_equiv(n as nat);
    string_seq
}
// </vc-code>

} // verus!
fn main() {}