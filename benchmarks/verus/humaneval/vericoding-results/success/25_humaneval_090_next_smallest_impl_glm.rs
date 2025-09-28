// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn get_val(mx: Option<int>) -> int
    recommends matches!(mx, Some(_))
{
    match mx {
        Some(n) => n,
        None => 0
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rolling_max(s: &Vec<i8>) -> (res: Option<i8>)
    ensures 
        matches!(res, None) <==> s@.len() < 2,
        matches!(res, Some(_)) ==> exists|x: int| 0 <= x < s@.len() && s@[x] as int == get_val(match res { Some(v) => Some(v as int), None => None }),
        forall|x: int, y: int| 0 <= x < y < s@.len() ==> s@[x] as int <= get_val(match res { Some(v) => Some(v as int), None => None }) || s@[y] as int <= get_val(match res { Some(v) => Some(v as int), None => None }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type cast issue in non-ghost code and added decreases clause */
    if s.len() < 2 {
        None
    } else {
        let mut max_val = s[0];
        let mut i = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                exists|j: int| 0 <= j < i && s@[j] as int == max_val as int,
                forall|j: int| 0 <= j < i ==> s@[j] as int <= max_val as int,
            decreases s.len() - i,
        {
            if s[i] > max_val {
                max_val = s[i];
            }
            i += 1;
        }
        Some(max_val)
    }
}
// </vc-code>


}

fn main() {}