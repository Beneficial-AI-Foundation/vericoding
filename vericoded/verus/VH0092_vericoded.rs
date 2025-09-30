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
/* helper modified by LLM (iteration 4): trivial lemma to keep helpers section valid */
proof fn triv_true()
    ensures
        true,
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
    /* code modified by LLM (iteration 4): implement second maximum with strong loop invariants; fix casting precedence with parentheses */
    if s.len() < 2 {
        return None;
    }

    let mut max1: i8 = s[0];
    let mut max2: i8 = s[1];
    let mut j1: usize = 0;
    let mut j2: usize = 1;

    if max2 > max1 {
        let tmp = max1;
        max1 = max2;
        max2 = tmp;
        j1 = 1;
        j2 = 0;
    } else {
        j1 = 0;
        j2 = 1;
    }

    let mut i: usize = 2;
    while i < s.len()
        invariant
            s@.len() >= 2,
            2 <= (i as int),
            (i as int) <= s@.len(),
            0 <= (j1 as int),
            (j1 as int) < (i as int),
            0 <= (j2 as int),
            (j2 as int) < (i as int),
            s@[(j1 as int)] as int == max1 as int,
            s@[(j2 as int)] as int == max2 as int,
            max1 as int >= max2 as int,
            forall|k: int| 0 <= k && k < (i as int) ==> s@[k] as int <= max1 as int,
            forall|k: int| 0 <= k && k < (i as int) ==> k == (j1 as int) || s@[k] as int <= max2 as int,
        decreases s@.len() - (i as int)
    {
        let v = s[i];
        if v >= max1 {
            max2 = max1;
            max1 = v;
            j2 = j1;
            j1 = i;
        } else if v > max2 {
            max2 = v;
            j2 = i;
        } else {
            // no change
        }
        i = i + 1;
    }

    Some(max2)
}
// </vc-code>


}

fn main() {}