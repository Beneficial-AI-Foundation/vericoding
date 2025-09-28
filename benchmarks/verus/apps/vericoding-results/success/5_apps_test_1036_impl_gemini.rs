// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn winner(a: char, b: char) -> char {
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') {
        b
    } else {
        a
    }
}

spec fn valid_rps_char(c: char) -> bool {
    c == 'R' || c == 'P' || c == 'S'
}

spec fn valid_rps_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> valid_rps_char(s[i])
}

spec fn valid_input(n: int, k: int, s: Seq<char>) -> bool {
    n > 0 && k >= 0 && s.len() == n && valid_rps_string(s)
}
// </vc-preamble>

// <vc-helpers>
fn rps_winner_exec(a: char, b: char) -> (res: char)
    requires
        valid_rps_char(a),
        valid_rps_char(b),
    ensures
        res == winner(a, b),
        valid_rps_char(res),
{
    if (a == 'R' && b == 'P') || (a == 'P' && b == 'S') || (a == 'S' && b == 'R') {
        b
    } else {
        a
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, s: Vec<char>) -> (result: char)
    requires valid_input(n as int, k as int, s@)
    ensures valid_rps_char(result)
// </vc-spec>
// <vc-code>
{
    let mut current_s = s;
    let mut i: i8 = 0;
    while i < k
        invariant
            0 <= i <= k,
            current_s.len() == n as nat,
            valid_rps_string(current_s@),
            n > 0,
        decreases k - i
    {
        let prev_s = current_s;
        let mut next_s = Vec::new();
        let mut j: i8 = 0;
        while j < n
            invariant
                0 <= j <= n,
                prev_s.len() == n as nat,
                valid_rps_string(prev_s@),
                next_s.len() == j as nat,
                valid_rps_string(next_s@),
                n > 0,
            decreases n - j
        {
            let c1 = prev_s[j as usize];
            let c2_idx = if j + 1 == n { 0 } else { j + 1 };
            let c2 = prev_s[c2_idx as usize];
            let w = rps_winner_exec(c1, c2);
            next_s.push(w);
            j = j + 1;
        }
        current_s = next_s;
        i = i + 1;
    }
    current_s[0]
}
// </vc-code>


}

fn main() {}