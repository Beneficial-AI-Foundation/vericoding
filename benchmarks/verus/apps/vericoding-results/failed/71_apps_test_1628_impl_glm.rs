// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'x' || s[i] == 'y'
}

spec fn count_char(s: Seq<char>, c: char) -> nat {
    s.filter(|x: char| x == c).len()
}

spec fn valid_output(s: Seq<char>, result: Seq<char>) -> bool 
    recommends valid_input(s)
{
    let count_x = count_char(s, 'x');
    let count_y = count_char(s, 'y');
    if count_y > count_x {
        result.len() == count_y - count_x && forall|i: int| 0 <= i < result.len() ==> result[i] == 'y'
    } else {
        result.len() == count_x - count_y && forall|i: int| 0 <= i < result.len() ==> result[i] == 'x'
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ensures clause and changed create_repeated_vec to take int */
fn count_chars(s: &Vec<char>) -> (nat, nat)
    ensures 
        result.0 == count_char(s@, 'x') && result.1 == count_char(s@, 'y')
{
    let mut x = 0;
    let mut y = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            x == count_char(s@.subrange(0, i as int), 'x'),
            y == count_char(s@.subrange(0, i as int), 'y'),
    {
        if s[i] == 'x' {
            x += 1;
        } else {
            y += 1;
        }
        i += 1;
    }
    (x, y)
}

fn create_repeated_vec(c: char, n: int) -> (v: Vec<char>)
    requires n >= 0
    ensures v@ == Seq::new(n, |j: int| c)
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            v@ == Seq::new(i, |j: int| c),
    {
        v.push(c);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): updated to work with fixed helper function */
    let (count_x, count_y) = count_chars(&s);
    let (output_char, diff) = if count_y > count_x {
        ('y', count_y - count_x)
    } else {
        ('x', count_x - count_y)
    };
    create_repeated_vec(output_char, diff)
}
// </vc-code>


}

fn main() {}