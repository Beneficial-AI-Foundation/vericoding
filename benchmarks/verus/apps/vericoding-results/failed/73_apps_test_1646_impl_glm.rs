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
/* helper modified by LLM (iteration 5): fixed overflow and invariant by using int for count and i, and added precondition v.len()<=100 */
fn count_zeros_exec(v: Vec<char>) -> (count: usize)
    requires
        valid_binary_string(v@),
        v.len() <= 100,
    ensures
        (count as int) == count_zeros(v@),
{
    let mut count: int = 0;
    let mut i: int = 0;
    let len = v.len() as int;
    while i < len
        invariant
            0 <= i <= len,
            count == count_zeros(v@.subrange(0, i)),
        decreases len - i,
    {
        if v[i as usize] == '0' {
            count += 1;
        }
        i += 1;
    }
    count as usize
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
/* code modified by LLM (iteration 5): fixed loop in else branch to use int for i and ensure proper casting */
{
    if s.len() == 1 && s[0] == '0' {
        vec!['0']
    } else {
        let zero_count = count_zeros_exec(s);
        let mut result = Vec::new();
        result.push('1');
        let mut i: int = 0;
        while i < zero_count as int
            invariant
                0 <= i <= zero_count as int,
                result@ == seq!['1'] + create_zero_seq(i as nat),
            decreases zero_count as int - i,
        {
            result.push('0');
            i += 1;
        }
        result
    }
}
// </vc-code>


}

fn main() {}