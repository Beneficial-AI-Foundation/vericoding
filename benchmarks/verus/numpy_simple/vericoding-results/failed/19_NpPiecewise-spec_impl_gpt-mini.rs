// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): find first matching condition returning index or -1 */
spec fn find_first(conds: &Vec<spec_fn(f32) -> bool>, xi: f32) -> int
    ensures
        (result >= 0 && result < conds@.len() && conds@[result](xi)) ||
        (result == -1 && forall|h: int| 0 <= h && h < conds@.len() ==> !conds@[h](xi)),
{
    find_first_from(conds, xi, 0)
}

/* helper modified by LLM (iteration 5): recursive search starting at index i */
spec fn find_first_from(conds: &Vec<spec_fn(f32) -> bool>, xi: f32, i: int) -> int
    requires
        0 <= i && i <= conds@.len(),
    ensures
        (result >= i && result < conds@.len() && conds@[result](xi)) ||
        (result == -1 && forall|h: int| i <= h && h < conds@.len() ==> !conds@[h](xi)),
    decreases
        conds@.len() - i
{
    if i >= conds@.len() {
        -1
    } else if conds@[i](xi) {
        i
    } else {
        find_first_from(conds, xi, i + 1)
    }
}

// </vc-helpers>

// <vc-spec>
fn piecewise(x: Vec<f32>, condlist: Vec<spec_fn(f32) -> bool>, funclist: Vec<spec_fn(f32) -> f32>) -> (ret: Vec<f32>)
    requires condlist@.len() == funclist@.len(),
    ensures
        ret@.len() == x@.len(),
        forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < condlist@.len() && 
            condlist@[j](x@[i]) ==> ret@[i] == funclist@[j](x@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement piecewise mapping using nested loops */
    let mut ret: Vec<f32> = Vec::new();

    let mut idx: usize = 0;
    while idx < x.len()
        invariant
            idx <= x.len(),
            ret.len() == idx,
        decreases
            x.len() - idx
    {
        let xi: f32 = x.get(idx);

        let mut j: usize = 0;
        let mut found_index: Option<usize> = None;
        while j < condlist.len()
            invariant
                j <= condlist.len(),
                match found_index {
                    None => forall|h: int| 0 <= h && h < (j as int) ==> !condlist@[h](xi),
                    Some(k) => 0 <= (k as int) && (k as int) < condlist@.len() && condlist@[(k as int)](xi),
                },
            decreases
                condlist.len() - j
        {
            if condlist.get(j)(xi) {
                found_index = Some(j);
                j = condlist.len();
            } else {
                j += 1;
            }
        }

        match found_index {
            Some(k) => {
                let v: f32 = funclist.get(k)(xi);
                ret.push(v);
            }
            None => {
                ret.push(0.0_f32);
            }
        }

        idx += 1;
    }

    ret
}

// </vc-code>


}
fn main() {}