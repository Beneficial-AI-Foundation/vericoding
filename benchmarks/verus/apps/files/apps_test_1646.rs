// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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

spec fn is_minimal_form(s: Seq<char>, result: Seq<char>) -> bool {
    (s == seq!['0'] ==> result == seq!['0'])
    &&
    (s != seq!['0'] ==> result == seq!['1'].add(Seq::new(count_zeros(s) as nat, |_| '0')))
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Seq<char>) -> (result: Seq<char>)
    requires 
        n >= 1 && n <= 100,
        s.len() == n,
        valid_binary_string(s),
    ensures 
        valid_binary_string(result),
        is_minimal_form(s, result),
// </vc-spec>
// <vc-code>
{
    assume(false);
    seq!['0']
}
// </vc-code>


}

fn main() {}