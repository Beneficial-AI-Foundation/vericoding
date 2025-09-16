// <vc-preamble>
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

spec fn number_to_char(n: nat) -> (result:Seq<char>)
    decreases n,
{
    if (n == 0) {
        seq![]
    } else {
        number_to_char(n / 10).add(seq![single_digit_number_to_char(n % 10)])
    }
}

spec fn string_sequence(n: nat) -> (result:Seq<char>)
    decreases n,
{
    if n == 0 {
        seq!['0']
    } else {
        string_sequence((n - 1) as nat).add(seq![' '].add(number_to_char(n)))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix old usage to reference the old vector then take its view; keep u16 helpers */
fn single_digit_number_to_char_exec_u16(d: u16) -> (result: char)
    requires
        d < 10,
    ensures
        result == single_digit_number_to_char(d as nat),
{
    if d == 0 { '0' }
    else if d == 1 { '1' }
    else if d == 2 { '2' }
    else if d == 3 { '3' }
    else if d == 4 { '4' }
    else if d == 5 { '5' }
    else if d == 6 { '6' }
    else if d == 7 { '7' }
    else if d == 8 { '8' }
    else { '9' }
}

/* helper modified by LLM (iteration 3): use (old(v))@ in ensures to avoid type mismatch; recursive build of digits */
fn push_number_to_vec_u16(v: &mut Vec<char>, k: u16)
    ensures
        v@ == (old(v))@.add(number_to_char(k as nat)),
    decreases k as nat,
{
    if k == 0u16 {
        // number_to_char(0) == empty, so do nothing
    } else {
        let q: u16 = k / 10u16;
        let r: u16 = k % 10u16;
        push_number_to_vec_u16(v, q);
        assert(r < 10u16);
        let ch = single_digit_number_to_char_exec_u16(r);
        v.push(ch);
    }
}
// </vc-helpers>

// <vc-spec>
fn string_sequence_impl(n: u8) -> (string_seq: Vec<char>)

    ensures
        string_seq@ == string_sequence(n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix invariant cast to nat after subtraction and rely on helper ensures */
    let mut string_seq: Vec<char> = Vec::new();
    string_seq.push('0');

    let mut i: u16 = 1u16;
    while i <= n as u16
        invariant
            string_seq@ == string_sequence((i - 1) as nat),
            1 <= i as nat,
            i as nat <= (n as nat) + 1,
        decreases ((n as nat) + 1) - (i as nat)
    {
        string_seq.push(' ');
        push_number_to_vec_u16(&mut string_seq, i);
        i = i + 1u16;
    }

    string_seq
}
// </vc-code>

}
fn main() {}