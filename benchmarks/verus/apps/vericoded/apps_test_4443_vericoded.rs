// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && 'a' <= input[0] <= 'y'
}

spec fn next_char(c: char) -> char
    recommends 'a' <= c <= 'y'
{
    ((c as u8) + 1) as char
}

spec fn valid_output(input: Seq<char>, output: Seq<char>) -> bool
    recommends valid_input(input)
{
    output.len() == 2 &&
    output[0] == next_char(input[0]) &&
    output[1] == '\n' &&
    'b' <= output[0] <= 'z'
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_next_char_in_bounds(c: char)
    requires
        'a' <= c <= 'y',
    ensures
        'b' <= next_char(c) <= 'z',
{
    match c {
        'a' => { assert(next_char('a') == 'b'); }
        'b' => { assert(next_char('b') == 'c'); }
        'c' => { assert(next_char('c') == 'd'); }
        'd' => { assert(next_char('d') == 'e'); }
        'e' => { assert(next_char('e') == 'f'); }
        'f' => { assert(next_char('f') == 'g'); }
        'g' => { assert(next_char('g') == 'h'); }
        'h' => { assert(next_char('h') == 'i'); }
        'i' => { assert(next_char('i') == 'j'); }
        'j' => { assert(next_char('j') == 'k'); }
        'k' => { assert(next_char('k') == 'l'); }
        'l' => { assert(next_char('l') == 'm'); }
        'm' => { assert(next_char('m') == 'n'); }
        'n' => { assert(next_char('n') == 'o'); }
        'o' => { assert(next_char('o') == 'p'); }
        'p' => { assert(next_char('p') == 'q'); }
        'q' => { assert(next_char('q') == 'r'); }
        'r' => { assert(next_char('r') == 's'); }
        's' => { assert(next_char('s') == 't'); }
        't' => { assert(next_char('t') == 'u'); }
        'u' => { assert(next_char('u') == 'v'); }
        'v' => { assert(next_char('v') == 'w'); }
        'w' => { assert(next_char('w') == 'x'); }
        'x' => { assert(next_char('x') == 'y'); }
        'y' => { assert(next_char('y') == 'z'); }
        _ => { }
    }
}

fn next_char_exec(c: char) -> (d: char)
    requires
        'a' <= c <= 'y',
    ensures
        d == next_char(c),
        'b' <= d <= 'z',
{
    let d = ((c as u8) + 1) as char;
    proof {
        lemma_next_char_in_bounds(c);
    }
    d
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    let c = input[0];
    let d = next_char_exec(c);
    let mut out: Vec<char> = Vec::new();
    out.push(d);
    out.push('\n');
    out
}
// </vc-code>


}

fn main() {}