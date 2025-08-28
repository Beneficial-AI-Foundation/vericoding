use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_strictly_increasing(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] < s[j]
}

spec fn is_non_decreasing(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] <= s[j]
}

spec fn contains_unique_elements_from(result: Seq<i32>, source: Seq<i32>) -> bool {
    forall|x: i32| result.contains(x) ==> source.contains(x)
}

spec fn all_unique_elements_included(result: Seq<i32>, source: Seq<i32>) -> bool {
    forall|i: int, x: i32| 
        0 <= i && i < source.len() && x == source[i] &&
        (i == 0 || source[i-1] != x) ==> result.contains(x)
}

spec fn find_first_occurrence(a: Seq<i32>, val: i32, end: int) -> int
    decreases end
{
    if end <= 0 {
        -1
    } else if a[end-1] == val && (end == 1 || a[end-2] != val) {
        end-1
    } else if a[end-1] == val {
        find_first_occurrence(a, val, end-1)
    } else {
        -1
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            is_strictly_increasing(result@),
            contains_unique_elements_from(result@, a@),
            forall|j: int| 0 <= j && j < i ==> 
                (j == 0 || a@[j-1] != a@[j]) ==> result@.contains(a@[j]),
    {
        if i == 0 || a[i-1] != a[i] {
            result.push(a[i]);
            
            proof {
                let old_result = result@.drop_last();
                assert(is_strictly_increasing(old_result));
                if result@.len() > 1 {
                    let last_idx = result@.len() - 1;
                    let second_last_idx = last_idx - 1;
                    
                    let first_occ = find_first_occurrence(a@, a@[i as int], i as int);
                    if first_occ >= 0 && result@.len() > 1 {
                        assert(a@[first_occ] < a@[i as int]);
                        assert(result@[second_last_idx] < result@[last_idx]);
                    }
                }
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}