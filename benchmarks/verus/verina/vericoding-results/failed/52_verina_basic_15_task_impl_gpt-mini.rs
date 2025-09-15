// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for consecutive element at index */
spec fn has_consecutive_at(a: &Vec<i32>, i: int) -> bool { 0 <= i && i < a.len() - 1 && a@[i] + 1 == a@[(i + 1) as int] }

/* helper modified by LLM (iteration 5): lemma that from has_consecutive_at yields existence */
proof fn found_index_implies_exists(a: &Vec<i32>, i: int)
    requires has_consecutive_at(a, i)
    ensures exists|j: int| { 0 <= j && j < a.len() - 1 && a@[j] + 1 == a@[(j + 1) as int] }
{
    proof {
        assert(has_consecutive_at(a, i));
        assert(exists|j: int| { j == i && 0 <= j && j < a.len() - 1 && a@[j] + 1 == a@[(j + 1) as int] });
    }
}
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): search for consecutive pair using loop and witness */
    let mut i: int = 0;
    let mut found: bool = false;
    let mut witness: int = 0;
    while i < a.len() - 1
        invariant 0 <= i && i <= a.len()
        invariant found || forall|j: int| 0 <= j && j < i ==> a@[j] + 1 != a@[(j + 1) as int]
        decreases a.len() - i
    {
        if a@[i] + 1 == a@[(i + 1) as int] {
            found = true;
            witness = i;
            i = a.len();
        } else {
            i = i + 1;
        }
    }

    let result = found;
    proof {
        if result {
            assert(0 <= witness);
            assert(witness < a.len() - 1);
            assert(a@[witness] + 1 == a@[(witness + 1) as int]);
            assert(exists|j: int| { 0 <= j && j < a.len() - 1 && a@[j] + 1 == a@[(j + 1) as int] });
        } else {
            assert(i >= a.len() - 1);
            assert(!found);
            assert(forall|j: int| 0 <= j && j < i ==> a@[j] + 1 != a@[(j + 1) as int]);
            assert(forall|j: int| 0 <= j && j < a.len() - 1 ==> a@[j] + 1 != a@[(j + 1) as int]);
            assert(! (exists|j: int| { 0 <= j && j < a.len() - 1 && a@[j] + 1 == a@[(j + 1) as int] }));
        }
    }

    result
}
// </vc-code>

}
fn main() {}