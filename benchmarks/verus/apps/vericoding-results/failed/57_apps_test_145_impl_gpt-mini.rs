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
/* helper modified by LLM (iteration 5): count_first computes number of distinct chars by scanning */
spec fn count_first(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let n = s.len();
        let s1 = s.subrange(0, n - 1);
        let last = s@[n - 1];
        count_first(s1) + if (forall|j: int| 0 <= j < n - 1 ==> s1@[j] != last) { 1 } else { 0 }
    }
}

/* helper modified by LLM (iteration 5): proof that count_first equals count_distinct */
proof fn count_first_eq_count_distinct(s: Seq<char>)
    ensures count_first(s) == count_distinct(s)
    decreases s.len()
{
    proof {
        if s.len() == 0 {
            assert(count_first(s) == 0);
            assert(count_distinct(s) == 0);
        } else {
            let n = s.len();
            let s1 = s.subrange(0, n - 1);
            count_first_eq_count_distinct(s1);
            let c = s@[n - 1];
            assert(count_first(s) == count_first(s1) + (if (forall|j: int| 0 <= j < n - 1 ==> s1@[j] != c) { 1 } else { 0 }));
            assert(s.to_set() == s1.to_set().insert(c));
            assert(count_distinct(s) == count_distinct(s1) + (if (c in s1.to_set()) { 0 } else { 1 }));
            if (forall|j: int| 0 <= j < n - 1 ==> s1@[j] != c) {
                assert(!(c in s1.to_set()));
                assert(count_first(s) == count_first(s1) + 1);
                assert(count_distinct(s) == count_distinct(s1) + 1);
                assert(count_first(s) == count_distinct(s));
            } else {
                assert(count_first(s) == count_first(s1));
                assert(count_distinct(s) == count_distinct(s1));
                assert(count_first(s) == count_distinct(s));
            }
        }
    }
}

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
/* code modified by LLM (iteration 5): compute distinct count and produce output */
{
    let username_len: int = input@.len() - 1;
    let username = input@.subrange(0, username_len);
    let mut output: Vec<char> = Vec::new();
    let mut count: int = 0;
    let mut i: int = 0;
    while i < username_len
        invariant
            0 <= i <= username_len,
            count == count_first(input@.subrange(0, i)),
        decreases username_len - i
    {
        let mut first: bool = true;
        let mut j: int = 0;
        while j < i
            invariant
                0 <= j <= i,
                first == (forall|q: int| 0 <= q < j ==> input@[q] != input@[i]),
            decreases i - j
        {
            if input@[j] == input@[i] {
                first = false;
            }
            j = j + 1;
        }
        if first {
            count = count + 1;
        }
        i = i + 1;
    }

    proof {
        count_first_eq_count_distinct(username);
        assert(count == count_first(username));
        assert(count == count_distinct(username));
    }

    if count % 2 == 1 {
        output.push('I');
        output.push('G');
        output.push('N');
        output.push('O');
        output.push('R');
        output.push('E');
        output.push(' ');
        output.push('H');
        output.push('I');
        output.push('M');
        output.push('!');
        output.push('\n');
    } else {
        output.push('C');
        output.push('H');
        output.push('A');
        output.push('T');
        output.push(' ');
        output.push('W');
        output.push('I');
        output.push('T');
        output.push('H');
        output.push(' ');
        output.push('H');
        output.push('E');
        output.push('R');
        output.push('!');
        output.push('\n');
    }

    output
}

// </vc-code>


}

fn main() {}