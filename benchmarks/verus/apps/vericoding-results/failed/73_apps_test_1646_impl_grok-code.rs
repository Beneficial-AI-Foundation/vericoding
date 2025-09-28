// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_binary_string(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1') &&
    (s == seq!['0'] || s[0] == '1')
}

spec fn count_zeros(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0int
    } else { 
        (if s[0] == '0' { 1int } else { 0int }) + count_zeros(s.subrange(1, s.len() as int))
    }
}

spec fn create_zero_seq(n: nat) -> Seq<char> {
    Seq::new(n, |i: int| '0')
}

spec fn is_minimal_form(s: Seq<char>, result: Seq<char>) -> bool {
    (s == seq!['0'] ==> result == seq!['0'])
    &&
    (s != seq!['0'] ==> result == seq!['1'] + create_zero_seq(count_zeros(s) as nat))
}
// </vc-preamble>

// <vc-helpers>
fn count_zeros_exec(v: &[char]) -> (result: usize)
    requires
        v@.len() <= 100,
    ensures
        count_zeros(v@) == result as int,
{
    let mut count = 0usize;
    let mut i = 0usize;
    while i < v.len()
        invariant
            count >= 0,
            i >= 0,
            i <= v.len(),
            count == count_zeros(v@.subrange(0, i as int)),
        decreases v.len() - i,
    {
        if v[i] == '0' {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, s: Vec<char>) -> (result: Vec<char>)
    requires 
        n >= 1 && n <= 100,
        s.len() == n as usize,
        valid_binary_string(s@),
    ensures 
        valid_binary_string(result@),
        is_minimal_form(s@, result@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation errors by using Vec for length and indexing in executable code instead of ghost Seq */
{
    if s.len() == 1 && s[0] == '0' {
        return vec!['0'];
    }
    let zeros = count_zeros_exec(&s);
    let mut result = Vec::new();
    result.push('1');
    let mut j = 0;
    while j < zeros as usize
        invariant
            result@ == seq!['1'] + create_zero_seq(j as nat),
            j <= zeros as usize,
        decreases zeros as usize - j,
    {
        result.push('0');
        j += 1;
    }
    result
}
// </vc-code>


}

fn main() {}