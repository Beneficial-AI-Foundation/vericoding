// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s.index(i) >= '1' && #[trigger] s.index(i) <= '9'
}

spec fn string_to_int(s: Seq<char>) -> int {
    100 * ((s.index(0) as int) - ('0' as int)) + 
    10 * ((s.index(1) as int) - ('0' as int)) + 
    ((s.index(2) as int) - ('0' as int))
}

spec fn abs_diff(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn substring_at_index(s: Seq<char>, i: int) -> Seq<char> {
    s.subrange(i, i + 3)
}

spec fn is_minimum_difference(s: Seq<char>, result: int) -> bool {
    valid_input(s) ==> (
        result >= 0 &&
        (exists|i: int| 0 <= i <= s.len() - 3 && result == abs_diff(753 - string_to_int(#[trigger] substring_at_index(s, i)))) &&
        (forall|i: int| 0 <= i <= s.len() - 3 ==> result <= abs_diff(753 - string_to_int(#[trigger] substring_at_index(s, i))))
    )
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i32)
    requires valid_input(s@)
    ensures is_minimum_difference(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed type error in sequence indexing */
    let mut min_diff: i32 = i32::MAX;
    let mut i: usize = 0;
    
    while i <= s.len() - 3
        invariant
            valid_input(s@),
            0 <= i <= s.len() - 3 + 1,
            min_diff >= 0,
            forall|j: int| 0 <= j < i ==> min_diff as int <= abs_diff(753 - string_to_int(#[trigger] substring_at_index(s@, j))),
            i > 0 ==> exists|j: int| 0 <= j < i && min_diff as int == abs_diff(753 - string_to_int(#[trigger] substring_at_index(s@, j)))
    {
        let d1 = s[i] as i32 - '0' as i32;
        let d2 = s[i + 1] as i32 - '0' as i32;
        let d3 = s[i + 2] as i32 - '0' as i32;
        let num = 100 * d1 + 10 * d2 + d3;
        let diff = if 753 - num >= 0 { 753 - num } else { num - 753 };
        
        assert(s@[i as int] == s[i as usize]);
        assert(s@[i as int + 1] == s[i + 1]);
        assert(s@[i as int + 2] == s[i + 2]);
        assert(substring_at_index(s@, i as int) == s@.subrange(i as int, i as int + 3));
        assert(string_to_int(substring_at_index(s@, i as int)) == num as int);
        assert(diff as int == abs_diff(753 - num as int));
        
        if diff < min_diff {
            min_diff = diff;
        }
        
        i = i + 1;
    }
    
    min_diff
}
// </vc-code>


}

fn main() {}