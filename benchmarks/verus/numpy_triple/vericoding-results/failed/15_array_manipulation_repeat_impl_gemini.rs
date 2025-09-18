// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax of forall statement */
proof fn append_repeats_lemma<T>(prefix: Seq<T>, elt: T, a: Seq<T>, j: int, repeats: int)
    requires
        repeats > 0,
        j >= 0,
        j < a.len(),
        elt == a[j],
        prefix.len() == j * repeats,
        forall|i: int| 0 <= i < prefix.len() ==> {
            let k = i / repeats;
            0 <= k < j && prefix[i] == a[k]
        },
    ensures
        ({
            let suffix = Seq::new(repeats as nat, |l: int| elt);
            let result = prefix + suffix;
            result.len() == (j + 1) * repeats
            && forall|i: int| 0 <= i < result.len() ==> {
                let k = i / repeats;
                0 <= k < j + 1 && result[i] == a[k]
            }
        })
{
    let suffix = Seq::new(repeats as nat, |l: int| elt);
    let result = prefix + suffix;
    assert((j + 1) * repeats == j * repeats + repeats) by(nonlinear_arith)
        requires j >= 0, repeats > 0;
    assert(result.len() == (j + 1) * repeats);

    forall|i: int|
        ensures (0 <= i < result.len()) ==> 
        {
            let k = i / repeats;
            0 <= k < j + 1 && result[i] == a[k]
        }
    {
        let k = i / repeats;
        if i < prefix.len() {
            assert(k < j) by(nonlinear_arith)
                requires i < prefix.len(), prefix.len() == j * repeats, repeats > 0;
            assert(result[i] == prefix[i]);
            assert(prefix[i] == a[k]);
        } else {
            assert(k == j) by(nonlinear_arith)
                requires i >= prefix.len(), i < result.len(), prefix.len() == j*repeats, result.len() == (j+1)*repeats, repeats > 0;
            let suffix_idx = i - prefix.len();
            assert(result[i] == suffix[suffix_idx]);
            assert(suffix[suffix_idx] == elt);
            assert(result[i] == a[j]);
            assert(result[i] == a[k]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn repeat<T: Copy>(a: Vec<T>, repeats: usize) -> (result: Vec<T>)
    requires repeats > 0,
    ensures
        result.len() == a.len() * repeats,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let k = i / (repeats as int);
            0 <= k < a.len() && result[i] == a[k]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): moved proof function call into a proof block */
{
    let mut result: Vec<T> = Vec::new();
    let mut j: usize = 0;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            result.len() == j * repeats,
            forall|i: int| #![trigger result@[i]] 0 <= i < result.len() ==> {
                let k = i / (repeats as int);
                0 <= k < j && result@[i] == a@[k]
            },
        decreases a.len() - j
    {
        let old_result_view = result.view();
        let elt_to_add = a[j];

        let mut l: usize = 0;
        while l < repeats
            invariant
                j < a.len(),
                0 <= l <= repeats,
                result.len() == old_result_view.len() + l,
                result.view().subrange(0, old_result_view.len()) == old_result_view,
                forall|i: int| old_result_view.len() <= i < result.len() ==> result@[i] == elt_to_add,
            decreases repeats - l
        {
            result.push(elt_to_add);
            l = l + 1;
        }

        proof {
            let suffix = Seq::new(repeats as nat, |_| elt_to_add);
            assert(result.view() =~= old_result_view + suffix);
            append_repeats_lemma::<T>(old_result_view, elt_to_add, a.view(), j as int, repeats as int);
        }

        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}