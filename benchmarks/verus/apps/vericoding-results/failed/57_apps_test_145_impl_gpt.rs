// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_distinct(s: Seq<char>) -> int {
    s.to_set().len() as int
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    input[input.len() - 1] == '\n' &&
    input.len() >= 2 &&
    forall|i: int| 0 <= i < input.len() - 1 ==> 'a' <= input[i] && input[i] <= 'z'
}

spec fn correct_output(username: Seq<char>, output: Seq<char>) -> bool {
    let distinct_count = count_distinct(username);
    (distinct_count % 2 == 1 ==> output == seq!['I', 'G', 'N', 'O', 'R', 'E', ' ', 'H', 'I', 'M', '!', '\n']) &&
    (distinct_count % 2 == 0 ==> output == seq!['C', 'H', 'A', 'T', ' ', 'W', 'I', 'T', 'H', ' ', 'H', 'E', 'R', '!', '\n'])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no additional helpers required for this iteration; placeholder helper to keep section valid */
proof fn helper_noop() { }
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures ({
        let username = input@.subrange(0, input@.len() - 1);
        correct_output(username, output@)
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): removed spec variable usage in exec code; use input@ directly in invariants */
{
    let n = input.len();
    let m_usize = n - 1;

    let mut par: bool = false;
    let mut j: usize = 0;
    while j < m_usize
        invariant
            j <= m_usize,
            par == (((input@.subrange(0, j as int)).to_set().len() as int) % 2 == 1),
        decreases (m_usize - j) as int
    {
        let cj = input[j];
        let mut i: usize = 0;
        let mut seen_before: bool = false;
        while i < j
            invariant
                i <= j,
                seen_before == (exists|k: int| 0 <= k < i as int && input@[k] == cj),
            decreases (j - i) as int
        {
            if input[i] == cj {
                seen_before = true;
            }
            i += 1;
        }
        if !seen_before {
            par = !par;
        }
        j += 1;
    }

    let mut out: Vec<char> = Vec::new();
    if par {
        out.push('I'); out.push('G'); out.push('N'); out.push('O'); out.push('R'); out.push('E'); out.push(' ');
        out.push('H'); out.push('I'); out.push('M'); out.push('!'); out.push('\n');
    } else {
        out.push('C'); out.push('H'); out.push('A'); out.push('T'); out.push(' ');
        out.push('W'); out.push('I'); out.push('T'); out.push('H'); out.push(' ');
        out.push('H'); out.push('E'); out.push('R'); out.push('!'); out.push('\n');
    }

    out
}
// </vc-code>


}

fn main() {}