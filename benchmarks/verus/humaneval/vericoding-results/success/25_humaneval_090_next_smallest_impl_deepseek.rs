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

spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

proof fn rolling_max_proof(s: Seq<i8>, i: int, current_max: int)
    requires
        0 <= i <= s.len(),
        forall|j: int| 0 <= j < i ==> s[j] as int <= current_max,
        i > 0 ==> exists|j: int| 0 <= j < i && s[j] as int == current_max
    ensures
        forall|j: int| 0 <= j < i ==> s[j] as int <= current_max,
        i > 0 ==> exists|j: int| 0 <= j < i && s[j] as int == current_max
{
}

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
    if s.len() < 2 {
        None
    } else {
        let mut max_val = s[0] as i8;
        let mut i: usize = 1;
        
        while i < s.len()
            invariant
                i >= 1,
                i <= s.len(),
                forall|j: int| 0 <= j < i ==> s@[j] as int <= max_val as int,
                exists|j: int| 0 <= j < i && s@[j] as int == max_val as int
            decreases s.len() - i
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