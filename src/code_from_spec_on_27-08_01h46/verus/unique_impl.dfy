use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_unique(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] != s[j]
}

spec fn is_sorted_strict(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] < s[j]
}

spec fn is_sorted_non_strict(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] <= s[j]
}

spec fn is_subsequence(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    forall|i: int| 0 <= i && i < s1.len() ==> exists|j: int| 0 <= j && j < s2.len() && s1[i] == s2[j]
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
            0 <= i <= a.len(),
            is_sorted_strict(result@),
            forall|k: int| 0 <= k && k < result.len() ==> 
                exists|j: int| 0 <= j && j < i && result@[k] == a[j],
            forall|j: int, k: int| 0 <= j && j < i && 0 <= k && k < result.len() && a[j] == result@[k] ==>
                forall|l: int| j < l && l < i ==> a[l] != a[j],
    {
        if result.len() == 0 || result@[result.len() as int - 1] != a[i] {
            result.push(a[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}