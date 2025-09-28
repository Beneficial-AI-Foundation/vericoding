// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compare substring at index using runtime loop and borrows */
fn equals_at(s: &Vec<char>, substr: &Vec<char>, i: usize) -> (res: bool)
    requires
        i + substr.len() <= s.len(),
    ensures
        res == (s@.subrange(i as int, i as int + substr@.len()) == substr@),
{
    let mut k: usize = 0;
    let mut res: bool = true;
    while k < substr.len()
        invariant
            k <= substr.len(),
            res == (s@.subrange(i as int, i as int + k as int) == substr@.subrange(0, k as int)),
        decreases
            substr.len() - k
    {
        if !(res && s[i + k] == substr[k]) {
            res = false;
        }
        k = k + 1;
    }
    res
}

// </vc-helpers>

// <vc-spec>
fn how_many_times(s: Vec<char>, substr: Vec<char>) -> (times: usize)
    ensures times == Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate through possible starts and count matches using equals_at with borrowed args */
    let n = s.len();
    let m = substr.len();
    if m > n {
        0
    } else {
        let max_start = n - m;
        let mut i: usize = 0;
        let mut count: usize = 0;
        while i <= max_start
            invariant
                0 <= i as int,
                count == Set::new(|j: int| 0 <= j && j < i as int && s@.subrange(j, j + m as int) == substr@).len(),
            decreases
                max_start - i
        {
            if equals_at(&s, &substr, i) {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}

// </vc-code>


}

fn main() {}