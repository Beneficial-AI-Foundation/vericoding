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

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by removing invalid ghost variable assignment in exec code and ensuring exec-spec compatibility. */
{
    let mut count_x: usize = 0;
    let mut count_y: usize = 0;
proof {
    reveal(valid_input);
    assert(valid_input(s@));
}
    let seq_len = s.len();
    let mut i: usize = 0;
while i < seq_len
    invariant
        count_x == count_char(s@.subrange(0, i as int), 'x'),
        count_y == count_char(s@.subrange(0, i as int), 'y'),
    decreases seq_len - i
{
    if s[i] == 'x' {
        count_x += 1;
    } else if s[i] == 'y' {
        count_y += 1;
    }
    i += 1;
}
let diff = if count_y > count_x { count_y - count_x } else { count_x - count_y };
    let c = if count_y > count_x { 'y' } else { 'x' };
    let mut result = Vec::new();
    let mut j: usize = 0;
while j < diff
    invariant
        result.len() == j as int,
        forall |k: int| 0 <= k < result.len() ==> result@[k] == c,
    decreases diff - j
{
    result.push(c);
    j += 1;
}
result
}
// </vc-code>


}

fn main() {}