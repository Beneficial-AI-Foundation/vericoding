// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that an insertion-built new vector contains all elements of the old vector and the inserted element */
fn lemma_insert_preserve(old: &Vec<i32>, newv: &Vec<i32>, x: i32, pos: usize)
    requires
        pos <= old.len(),
        newv.len() == old.len() + 1,
        forall|k: int| 0 <= k && k < pos as int ==> newv@[k] == old@[k],
        newv@[pos as int] == x,
        forall|k: int| pos as int <= k && k < old.len() as int ==> newv@[k + 1] == old@[k],
    ensures
        forall|k: int| 0 <= k && k < old.len() as int ==> newv@.contains(old@[k]),
        newv@.contains(x),
{
    proof {
        // For every index in old, the corresponding element appears in newv at a known index
        assert(forall|k: int| 0 <= k && k < old.len() as int ==>
            if k < pos as int {
                newv@[k] == old@[k]
            } else {
                newv@[k + 1] == old@[k]
            }
        );
        // From the equalities above, deduce containment for each old element
        assert(forall|k: int| 0 <= k && k < old.len() as int ==> newv@.contains(old@[k]));
        // And the inserted element is present
        assert(newv@.contains(x));
    }
}

// </vc-helpers>

// <vc-spec>
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build a sorted unique vector by scanning and inserting while preserving membership and sortedness */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            res.len() <= arr.len(),
            forall|p: int| 0 <= p && p + 1 < res.len() as int ==> #[trigger] res@[p] <= res@[p + 1],
            forall|k: int| 0 <= k && k < i as int ==> res@.contains(arr@[k]),
        decreases arr.len() - i
    {
        let x: i32 = arr[i];
        // check whether x is already in res
        let mut j: usize = 0;
        while j < res.len()
            invariant
                j <= res.len(),
                forall|k: int| 0 <= k && k < j as int ==> res@[k] != x,
            decreases res.len() - j
        {
            if res[j] == x {
                break;
            }
            j = j + 1;
        }
        if j == res.len() {
            // need to insert x in sorted position
            let mut pos: usize = 0;
            while pos < res.len()
                invariant
                    pos <= res.len(),
                    forall|k: int| 0 <= k && k < pos as int ==> res@[k] < x,
                decreases res.len() - pos
            {
                if !(res[pos] < x) { break; }
                pos = pos + 1;
            }
            // snapshot old res to relate membership later
            let old = res.clone();
            // build new vector newv = old[0..pos] + [x] + old[pos..]
            let mut newv: Vec<i32> = Vec::new();
            let mut k: usize = 0;
            while k < pos
                invariant
                    k <= pos,
                    pos <= old.len(),
                    newv.len() == k,
                decreases pos - k
            {
                newv.push(old[k]);
                k = k + 1;
            }
            newv.push(x);
            let mut k2: usize = pos;
            while k2 < old.len()
                invariant
                    pos <= k2,
                    k2 <= old.len(),
                    newv.len() == (k2 + 1),
                decreases old.len() - k2
            {
                newv.push(old[k2]);
                k2 = k2 + 1;
            }
            // update res to be newv
            res = newv;
            proof {
                // show that the constructed new res has the structural properties required by lemma_insert_preserve
                assert(pos <= old.len());
                assert(res.len() == old.len() + 1);
                assert(forall|k: int| 0 <= k && k < pos as int ==> res@[k] == old@[k]);
                assert(res@[pos as int] == x);
                assert(forall|k: int| pos as int <= k && k < old.len() as int ==> res@[k + 1] == old@[k]);
                // apply lemma to conclude old elements are still present and x is present
                lemma_insert_preserve(&old, &res, x, pos);
                // using previous loop invariant that old contained processed arr[0..i), conclude new res contains them as well
                assert(forall|k: int| 0 <= k && k < i as int ==> res@.contains(arr@[k]));
                // sortedness is preserved: elements before pos are < x and elements after pos are >= x because they came from old
                assert(forall|p: int| 0 <= p && p + 1 < res.len() as int ==> res@[p] <= res@[p + 1]);
            }
        }
        i = i + 1;
    }
    res
}

// </vc-code>

}
fn main() {}