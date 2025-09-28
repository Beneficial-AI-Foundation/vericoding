// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate spec and exec equality at a given index for two vectors */
proof fn spec_exec_index_eq<T>(v1: &Vec<T>, v2: &Vec<T>, i: int)
    requires
        0 <= i,
        i < v1.len() as int,
        v1.len() == v2.len(),
    ensures
        (v1@[i] == v2@[i]) <==> (v1[i as usize] == v2[i as usize]),
    decreases 0
{
}

/* helper modified by LLM (iteration 5): extend prefix equality by one position */
proof fn extend_prefix_equality<T>(a1: &Vec<T>, a2: &Vec<T>, k: int)
    requires
        a1.len() == a2.len(),
        0 <= k,
        k < a1.len() as int,
        forall|j: int| 0 <= j < k ==> a1@[j] == a2@[j],
        a1@[k] == a2@[k],
    ensures
        forall|j: int| 0 <= j < k + 1 ==> a1@[j] == a2@[j],
    decreases 0
{
}

// </vc-helpers>

// <vc-spec>
fn array_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures 
        result == true <==> (forall|i: int| 0 <= i < a1.len() as int ==> a1@[i] == a2@[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() as int && !(a1@[i] == a2@[i]) ==> result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): preserve prefix-equality invariant via helper lemmas and connect exec/spec equality */
    let mut i: usize = 0;
    while i < a1.len()
        invariant
            a1.len() == a2.len(),
            i <= a1.len(),
            forall|j: int| 0 <= j < i as int ==> a1@[j] == a2@[j],
        decreases a1.len() as int - i as int
    {
        if !(a1[i] == a2[i]) {
            proof {
                let j: int = i as int;
                assert(0 <= j && j < a1.len() as int);
                spec_exec_index_eq(a1, a2, j);
                assert(!(a1@[j] == a2@[j]));
            }
            return false;
        } else {
            proof {
                let j: int = i as int;
                assert(0 <= j && j < a1.len() as int);
                spec_exec_index_eq(a1, a2, j);
                assert(a1@[j] == a2@[j]);
                extend_prefix_equality(a1, a2, j);
            }
            i += 1;
        }
    }
    proof {
        assert(i == a1.len());
        assert(forall|j: int| 0 <= j < a1.len() as int ==> a1@[j] == a2@[j]);
    }
    true
}
// </vc-code>

}
fn main() {}