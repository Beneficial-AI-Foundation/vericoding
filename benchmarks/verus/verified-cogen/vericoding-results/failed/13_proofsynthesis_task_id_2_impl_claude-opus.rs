// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_no_duplicates(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] != v[j]
}

proof fn lemma_push_maintains_no_duplicates(v: Seq<i32>, elem: i32)
    requires
        contains_no_duplicates(v),
        !v.contains(elem),
    ensures
        contains_no_duplicates(v.push(elem)),
{
    assert forall|i: int, j: int| 0 <= i < j < v.push(elem).len() implies v.push(elem)[i] != v.push(elem)[j] by {
        if j == v.len() {
            assert(v.push(elem)[j] == elem);
            if i < v.len() {
                assert(v.push(elem)[i] == v[i]);
                assert(!v.contains(elem));
            }
        } else {
            assert(v.push(elem)[i] == v[i]);
            assert(v.push(elem)[j] == v[j]);
        }
    }
}

/* helper modified by LLM (iteration 5): added spec function to track elements already processed */
spec fn already_processed(list1: Seq<i32>, shared: Seq<i32>, i: int) -> bool {
    forall|k: int| 0 <= k < i ==> !list2_contains(list1[k]) || shared.contains(list1[k])
}

spec fn list2_contains(elem: i32) -> bool;
// </vc-helpers>

// <vc-spec>
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed invariant for already processed elements */
{
    let mut shared = Vec::new();
    let mut i: usize = 0;
    
    while i < list1.len()
        invariant
            i <= list1.len(),
            forall|k: int| 0 <= k < shared.len() ==> list1@.contains(#[trigger] shared[k]) && list2@.contains(#[trigger] shared[k]),
            contains_no_duplicates(shared@),
            forall|k: int| 0 <= k < i ==> (!list2@.contains(list1@[k]) || shared@.contains(list1@[k])),
        decreases list1.len() - i
    {
        let elem = list1[i];
        let mut found_in_list2 = false;
        let mut j: usize = 0;
        
        while j < list2.len()
            invariant
                j <= list2.len(),
                found_in_list2 <==> exists|m: int| 0 <= m < j && list2@[m] == elem,
            decreases list2.len() - j
        {
            if list2[j] == elem {
                found_in_list2 = true;
            }
            j = j + 1;
        }
        
        if found_in_list2 {
            let mut already_in_shared = false;
            let mut k: usize = 0;
            
            while k < shared.len()
                invariant
                    k <= shared.len(),
                    already_in_shared <==> exists|m: int| 0 <= m < k && shared@[m] == elem,
                decreases shared.len() - k
            {
                if shared[k] == elem {
                    already_in_shared = true;
                }
                k = k + 1;
            }
            
            if !already_in_shared {
                proof {
                    lemma_push_maintains_no_duplicates(shared@, elem);
                }
                shared.push(elem);
            }
        }
        i = i + 1;
    }
    
    shared
}
// </vc-code>

}
fn main() {}