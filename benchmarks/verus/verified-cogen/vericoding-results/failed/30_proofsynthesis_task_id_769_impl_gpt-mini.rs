// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec predicate for membership */
spec fn vec_not_contains(v: &Vec<i32>, x: i32) -> bool { !v@.contains(#[trigger] x) }

/* helper modified by LLM (iteration 5): lemma that appending a new element preserves uniqueness */
spec fn append_preserves_unique(s: Seq<i32>, x: i32) -> bool {
    (forall|p: int, q: int| 0 <= p < q < s.len() ==> #[trigger] s[p] != #[trigger] s[q]) &&
    (forall|p: int| 0 <= p < s.len() ==> #[trigger] s[p] != #[trigger] x) ==> 
    (forall|p: int, q: int| 0 <= p < q < s.len() + 1 ==> (if q == s.len() { #[trigger] s[p] != #[trigger] x } else { #[trigger] s[p] != #[trigger] s[q] }))
}
// </vc-helpers>

// <vc-spec>
fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replace spec contains with explicit runtime scans */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            forall|k: int| 0 <= k < (i as int) ==> (!arr2@.contains(#[trigger] arr1@[k]) ==> res@.contains(arr1@[k])),
            forall|p: int, q: int| 0 <= p < q < (res.len() as int) ==> #[trigger] res@[p] != #[trigger] res@[q],
        decreases arr1.len() - i
    {
        let x = arr1[i];
        let mut found_in_arr2: bool = false;
        let mut ii: usize = 0;
        while ii < arr2.len()
            invariant
                ii <= arr2.len(),
            decreases arr2.len() - ii
        {
            if arr2[ii] == x {
                found_in_arr2 = true;
                ii = arr2.len();
            } else {
                ii = ii + 1;
            }
        }
        if !found_in_arr2 {
            let mut found_in_res: bool = false;
            let mut ri: usize = 0;
            while ri < res.len()
                invariant
                    ri <= res.len(),
                decreases res.len() - ri
            {
                if res[ri] == x {
                    found_in_res = true;
                    ri = res.len();
                } else {
                    ri = ri + 1;
                }
            }
            if !found_in_res {
                res.push(x);
            }
        }
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < arr2.len()
        invariant
            j <= arr2.len(),
            forall|k: int| 0 <= k < (j as int) ==> (!arr1@.contains(#[trigger] arr2@[k]) ==> res@.contains(arr2@[k])),
            forall|p: int, q: int| 0 <= p < q < (res.len() as int) ==> #[trigger] res@[p] != #[trigger] res@[q],
        decreases arr2.len() - j
    {
        let x = arr2[j];
        let mut found_in_arr1: bool = false;
        let mut ii: usize = 0;
        while ii < arr1.len()
            invariant
                ii <= arr1.len(),
            decreases arr1.len() - ii
        {
            if arr1[ii] == x {
                found_in_arr1 = true;
                ii = arr1.len();
            } else {
                ii = ii + 1;
            }
        }
        if !found_in_arr1 {
            let mut found_in_res: bool = false;
            let mut ri: usize = 0;
            while ri < res.len()
                invariant
                    ri <= res.len(),
                decreases res.len() - ri
            {
                if res[ri] == x {
                    found_in_res = true;
                    ri = res.len();
                } else {
                    ri = ri + 1;
                }
            }
            if !found_in_res {
                res.push(x);
            }
        }
        j = j + 1;
    }

    res
}
// </vc-code>

}
fn main() {}