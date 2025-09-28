// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn online_max(a: &Vec<i32>, x: usize) -> (result: (i32, usize))
    requires
        a.len() > 0,
        x < a.len(),
    ensures
        ({
            let (m, p) = result;
            x <= p && p < a.len()
            && (forall|i: int| 0 <= i < x ==> a[i] <= m)
            && (exists|i: int| 0 <= i < x && a[i] == m)
            && ((p < a.len() - 1) ==> (exists|i: int| x <= i <= p && a[i] > m))
            && ((forall|i: int| x <= i < a.len() ==> a[i] <= m) ==> p == a.len() - 1)
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches in invariants by removing 'as usize' casts in spec quantifiers and using 'as int' for exec vars like pos */
    let mut max_val: i32 = a[0];
    let mut pos: usize = 0;
    let mut i: usize = 1;
    while i < x
        invariant
            1 <= (i as int) && (i as int) <= (x as int),
            forall|j: int| 0 <= j < (i as int) ==> a[j] <= max_val,
            exists|j: int| 0 <= j < (i as int) && a[j] == max_val,
            0 <= (pos as int) && (pos as int) < (i as int) && a[pos as int] == max_val
        decreases x - i
    {
        if a[i] > max_val {
            max_val = a[i];
            pos = i;
        }
        i += 1;
    }
    let mut p: usize = 0;
    let mut found: bool = false;
    let mut j: usize = x;
    while j < a.len()
        invariant
            (x as int) <= (j as int) && (j as int) <= (a.len() as int),
            if found { (p as int) < (j as int) } else { true },
            !found ==> forall|k: int| (x as int) <= k < (j as int) ==> a[k] <= max_val
        decreases a.len() - j
    {
        if !found && a[j] > max_val {
            p = j;
            found = true;
        }
        j += 1;
    }
    let final_p = if found { p } else { a.len() - 1 };
    (max_val, final_p)
}
// </vc-code>

}
fn main() {}