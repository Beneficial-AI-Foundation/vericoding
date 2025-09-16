// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (result:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '<' => (x + 1, b),
                    '>' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}

spec fn spec_bracketing(brackets: Seq<char>) -> (result:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// </vc-preamble>

// <vc-helpers>
spec fn is_left(c: char) -> bool { c == '<' }
spec fn is_right(c: char) -> bool { c == '>' }
fn step_counter(x: int, ok: bool, c: char) -> (int, bool) { if c == '<' { (x + 1, ok) } else if c == '>' { (x - 1, ok && x - 1 >= 0) } else { (x, ok) } }
proof fn step_counter_agrees(x: int, ok: bool, c: char)
    ensures
        step_counter(x, ok, c)
        ==
        match c {
            '<' => (x + 1, ok),
            '>' => (x - 1, ok && x - 1 >= 0),
            _ => (x, ok),
        },
{ }
// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: &str) -> (ret: bool)

    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,

    ensures
        ret <==> spec_bracketing(brackets@),
// </vc-spec>
// <vc-code>
{
    let bytes = brackets.as_bytes();
    let mut i: usize = 0;
    let mut depth: i32 = 0;
    let mut ok: bool = true;
    while i < bytes.len()
        invariant
            i <= bytes.len(),
        decreases (bytes.len() - i) as int
    {
        let b = bytes[i];
        if b == b'<' {
            depth += 1;
        } else if b == b'>' {
            depth -= 1;
            if depth < 0 {
                ok = false;
            }
        }
        i += 1;
    }
    ok && depth == 0
}
// </vc-code>

}
fn main() {}