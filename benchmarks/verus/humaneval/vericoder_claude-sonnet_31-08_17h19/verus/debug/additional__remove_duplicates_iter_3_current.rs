use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
spec fn contains_all_from_slice(result: Seq<i32>, a: Seq<i32>, end: int) -> bool {
    forall|i: int| 0 <= i < end ==> in_array(a, a[i]) ==> in_array(result, a[i])
}

spec fn no_duplicates(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

spec fn contains_element(s: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == x
}

spec fn found_in_range(result: Seq<i32>, current: i32, j: int) -> bool {
    exists|k: int| 0 <= k < j && result[k] == current
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        a.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|k: int| #![auto] 0 <= k < result.len() ==> in_array(a@, result[k]),
            no_duplicates(result@),
            forall|k: int| #![auto] 0 <= k < i ==> in_array(a@, a[k as int]) ==> in_array(result@, a[k as int]),
    {
        let current = a[i];
        let mut found = false;
        
        assert(found == found_in_range(result@, current, 0));
        
        for j in 0..result.len()
            invariant
                forall|k: int| #![auto] 0 <= k < result.len() ==> in_array(a@, result[k]),
                no_duplicates(result@),
                forall|k: int| #![auto] 0 <= k < i ==> in_array(a@, a[k as int]) ==> in_array(result@, a[k as int]),
                found == found_in_range(result@, current, j as int),
        {
            if result[j] == current {
                found = true;
                assert(found_in_range(result@, current, (j + 1) as int));
            } else {
                assert(found == found_in_range(result@, current, (j + 1) as int));
            }
        }
        
        if !found {
            result.push(current);
            assert(in_array(result@, current));
            assert(in_array(a@, current));
        }
        
        assert(forall|k: int| #![auto] 0 <= k < (i + 1) ==> in_array(a@, a[k as int]) ==> in_array(result@, a[k as int]));
    }
    
    result
}
// </vc-code>

fn main() {}
}