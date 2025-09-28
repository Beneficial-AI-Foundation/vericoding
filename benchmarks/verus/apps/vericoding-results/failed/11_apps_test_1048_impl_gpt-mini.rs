// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if s[0] == c { 1int } else { 0int }) + count_char(s.subrange(1, s.len() as int), c)
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn valid_commands(commands: Seq<char>) -> bool {
    forall|i: int| 0 <= i < commands.len() ==> commands[i] == 'L' || commands[i] == 'R' || commands[i] == 'U' || commands[i] == 'D'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prefix_count returns count of char c in prefix */
spec fn prefix_count(s: Seq<char>, c: char, i: int) -> int
    decreases i, s.len()
{
    if 0 <= i && i <= s.len() {
        count_char(s.subrange(0, i), c)
    } else {
        0int
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, commands: Vec<char>) -> (result: usize)
    requires 
        n >= 0,
        commands@.len() == n,
        valid_commands(commands@)
    ensures 
        result >= 0,
        result <= n,
        result % 2 == 0,
        result as int == 2 * min(count_char(commands@, 'L'), count_char(commands@, 'R')) + 
                         2 * min(count_char(commands@, 'U'), count_char(commands@, 'D'))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): count command occurrences and compute result using min */
    let mut i: usize = 0;
    let mut l: usize = 0;
    let mut r: usize = 0;
    let mut u: usize = 0;
    let mut d: usize = 0;

    while i < n
        invariant
            i <= n,
            (l as int) == prefix_count(commands@, 'L', i as int),
            (r as int) == prefix_count(commands@, 'R', i as int),
            (u as int) == prefix_count(commands@, 'U', i as int),
            (d as int) == prefix_count(commands@, 'D', i as int),
            l + r + u + d == i,
        decreases n - i
    {
        let ch = commands[i];
        if ch == 'L' {
            l = l + 1;
        } else if ch == 'R' {
            r = r + 1;
        } else if ch == 'U' {
            u = u + 1;
        } else {
            d = d + 1;
        }
        i = i + 1;
    }

    let lr = if l <= r { l } else { r };
    let ud = if u <= d { u } else { d };
    let result: usize = 2usize * lr + 2usize * ud;

    proof {
        assert(i == n);
        assert((l as int) + (r as int) + (u as int) + (d as int) == i as int);
        assert((lr as int) == min(l as int, r as int));
        assert((ud as int) == min(u as int, d as int));
        assert(result as int == 2int * min(l as int, r as int) + 2int * min(u as int, d as int));
        assert(result as int >= 0);
        assert(result <= n as int);
    }

    result
}
// </vc-code>


}

fn main() {}