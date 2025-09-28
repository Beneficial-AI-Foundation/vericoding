// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, s: Seq<char>) -> bool {
    n > 0 && k >= 0 && s.len() == n && 
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]) == '0' || s[i] == '1'
}

spec fn string_to_bits(s: Seq<char>) -> Seq<int>
    recommends forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
{
    Seq::new(s.len(), |i: int| if s[i] == '0' { 0 } else { 1 })
}

spec fn valid_result(result: int, n: int) -> bool {
    0 <= result <= n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, s: Vec<char>) -> (result: i8)
    requires valid_input(n as int, k as int, s@)
    ensures valid_result(result as int, n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut count: i8 = 0;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            0 <= i <= n as int,
            0 <= count <= i,
            n as int == s.len(),
            valid_input(n as int, k as int, s@),
        decreases n as int - i as int
    {
        if s[i] == '1' {
            count = count + 1;
        }
        i = i + 1;
    }
    
    if count >= k {
        count
    } else {
        0
    }
}
// </vc-code>


}

fn main() {}