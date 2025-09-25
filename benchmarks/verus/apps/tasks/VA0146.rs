// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_sf_flights(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() <= 1 { 
        0 
    } else { 
        (if s[s.len()-1] == 'F' && s[s.len()-2] != 'F' { 1int } else { 0int }) + count_sf_flights(s.subrange(0, s.len()-1))
    }
}

spec fn count_fs_flights(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() <= 1 { 
        0 
    } else { 
        (if s[s.len()-1] == 'S' && s[s.len()-2] != 'S' { 1int } else { 0int }) + count_fs_flights(s.subrange(0, s.len()-1))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: Vec<char>)
    requires 
        n >= 2,
        s@.len() == n,
        forall|i: int| 0 <= i < s@.len() ==> s@[i] == 'S' || s@[i] == 'F',
    ensures 
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        (result@ == seq!['Y', 'E', 'S']) <==> count_sf_flights(s@) > count_fs_flights(s@),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}