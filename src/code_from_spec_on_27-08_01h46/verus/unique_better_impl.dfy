use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_unique(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] != s[j]
}

spec fn is_strictly_increasing(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] < s[j]
}

spec fn is_subsequence_of(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    forall|i: int| 
        #![trigger s1[i]]
        0 <= i && i < s1.len() ==> exists|j: int| 0 <= j && j < s2.len() && s1[i] == s2[j]
}

proof fn sorted_implies_unique_is_strictly_increasing(s: Seq<i32>)
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] <= s[j],
        is_unique(s),
    ensures
        is_strictly_increasing(s),
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
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
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            forall|k: int, l: int| 0 <= k && k < l && l < result.len() ==> result@[k] < result@[l],
            forall|k: int| 
                #![trigger result@[k]]
                0 <= k && k < result.len() ==> 
                exists|j: int| 0 <= j && j < i && result@[k] == a[j],
            forall|k: int| 0 <= k && k < result.len() ==> 
                forall|l: int| 0 <= l && l < result.len() && k != l ==> result@[k] != result@[l],
            forall|k: int| 0 <= k && k < i ==> 
                (exists|l: int| 0 <= l && l < result.len() && a[k] == result@[l]) ||
                (exists|j: int| 0 <= j && j < k && a[j] == a[k]),
        decreases a.len() - i,
    {
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j && j <= result.len(),
                found <==> exists|k: int| 0 <= k && k < j && result@[k] == a[i as int],
                !found ==> forall|k: int| 0 <= k && k < j ==> result@[k] != a[i as int],
            decreases result.len() - j,
        {
            if result[j] == a[i] {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            result.push(a[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}