// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}

spec fn shift32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}

spec fn is_lower_case(c: char) -> (result:bool) {
    c >= 'a' && c <= 'z'
}

spec fn shift_minus_32_spec(c: char) -> (result:char) {
    ((c as u8) - 32) as char
}

spec fn to_toggle_case_spec(s: char) -> (result:char) {
    if is_lower_case(s) {
        shift_minus_32_spec(s)
    } else if is_upper_case(s) {
        shift32_spec(s)
    } else {
        s
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): rename return to `ret` to use in ensures; exhaustive ASCII toggle via match without spec calls */
fn to_toggle_char_exec(c: char) -> (ret: char)
    ensures
        ret == to_toggle_case_spec(c)
{
    match c {
        'a' => 'A',
        'b' => 'B',
        'c' => 'C',
        'd' => 'D',
        'e' => 'E',
        'f' => 'F',
        'g' => 'G',
        'h' => 'H',
        'i' => 'I',
        'j' => 'J',
        'k' => 'K',
        'l' => 'L',
        'm' => 'M',
        'n' => 'N',
        'o' => 'O',
        'p' => 'P',
        'q' => 'Q',
        'r' => 'R',
        's' => 'S',
        't' => 'T',
        'u' => 'U',
        'v' => 'V',
        'w' => 'W',
        'x' => 'X',
        'y' => 'Y',
        'z' => 'Z',
        'A' => 'a',
        'B' => 'b',
        'C' => 'c',
        'D' => 'd',
        'E' => 'e',
        'F' => 'f',
        'G' => 'g',
        'H' => 'h',
        'I' => 'i',
        'J' => 'j',
        'K' => 'k',
        'L' => 'l',
        'M' => 'm',
        'N' => 'n',
        'O' => 'o',
        'P' => 'p',
        'Q' => 'q',
        'R' => 'r',
        'S' => 's',
        'T' => 't',
        'U' => 'u',
        'V' => 'v',
        'W' => 'w',
        'X' => 'x',
        'Y' => 'y',
        'Z' => 'z',
        _ => c,
    }
}
// </vc-helpers>

// <vc-spec>
fn to_toggle_case(str1: &Vec<char>) -> (toggle_case: Vec<char>)

    ensures
        str1@.len() == toggle_case@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented loop building output using helper and added necessary invariants */
    let n = str1.len();
    let mut out: Vec<char> = Vec::new();
    out.reserve(n);

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == str1.len(),
            out.len() == i,
            forall|k: int| 0 <= k < i as int ==> out[k] == to_toggle_case_spec(#[trigger] str1[k])
        decreases n - i
    {
        let c = str1[i];
        let t = to_toggle_char_exec(c);
        out.push(t);
        i = i + 1;
    }

    out
}
// </vc-code>

}
fn main() {}