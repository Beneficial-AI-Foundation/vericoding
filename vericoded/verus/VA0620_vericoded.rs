// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_postal_code(a: int, b: int, s: Seq<char>) -> bool
    recommends a >= 1 && b >= 1 && a <= 5 && b <= 5,
              s.len() == a + b + 1,
              forall|i: int| 0 <= i < s.len() ==> (s[i] == '-' || ('0' <= s[i] <= '9'))
{
    s[a] == '-' && forall|i: int| 0 <= i < s.len() && i != a ==> s[i] != '-'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, s: Vec<char>) -> (result: Vec<char>)
    requires a as int >= 1 && b as int >= 1,
             a as int <= 5 && b as int <= 5,
             s@.len() == a as int + b as int + 1,
             forall|i: int| 0 <= i < s@.len() ==> (s@[i] == '-' || ('0' <= s@[i] <= '9'))
    ensures result@.len() >= 2,
            (result@ =~= seq!['Y', 'e', 's']) || (result@ =~= seq!['N', 'o']),
            (result@ =~= seq!['Y', 'e', 's']) <==> valid_postal_code(a as int, b as int, s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fix invariant logic for dash counting */
    let mut dash_count: usize = 0;
    let mut dash_pos: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            dash_count <= 1,
            dash_count == 1 ==> dash_pos < i,
            dash_count == 1 ==> s@[dash_pos as int] == '-',
            dash_count == 1 ==> forall|j: int| 0 <= j < i && j != dash_pos as int ==> s@[j] != '-',
            dash_count == 0 ==> forall|j: int| 0 <= j < i ==> s@[j] != '-',
        decreases s.len() - i
    {
        let c = s[i];
        if c == '-' {
            if dash_count == 0 {
                dash_count = 1;
                dash_pos = i;
            } else {
                // Found second dash, exit early
                return vec!['N', 'o'];
            }
        }
        i = i + 1;
    }
    
    if dash_count == 1 && dash_pos == a as usize {
        vec!['Y', 'e', 's']
    } else {
        vec!['N', 'o']
    }
}
// </vc-code>


}

fn main() {}