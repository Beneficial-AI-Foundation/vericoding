use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn sorted_sublist(s: Seq<i32>, start: int, end: int) -> bool {
    forall|i: int, j: int| 
        (#[trigger] s[i], #[trigger] s[j]) 
        start <= i && i < j && j < end ==> s[i] <= s[j]
}

proof fn sorted_sublist_transitive(s: Seq<i32>, a: int, b: int, c: int)
    requires
        sorted_sublist(s, a, b),
        sorted_sublist(s, b, c),
        a <= b && b <= c,
    ensures
        sorted_sublist(s, a, c),
{
}

spec fn unique_seq(s: Seq<i32>, start: int, end: int) -> bool {
    forall|i: int, j: int| 
        (#[trigger] s[i], #[trigger] s[j]) 
        start <= i && i < j && j < end ==> s[i] != s[j]
}

proof fn unique_seq_subrange(s: Seq<i32>, a: int, b: int, c: int)
    requires
        unique_seq(s, a, c),
        a <= b && b <= c,
    ensures
        unique_seq(s, a, b) && unique_seq(s, b, c),
{
}

spec fn contains_leq(s: Seq<i32>, val: i32, start: int, end: int) -> bool {
    exists|i: int| start <= i && i < end && s[i] <= val
}

spec fn contains_geq(s: Seq<i32>, val: i32, start: int, end: int) -> bool {
    exists|i: int| start <= i && i < end && s[i] >= val
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
    let mut i: usize = 0;
    
    while i < a.len() {
        body_invariant!(0 <= i && i <= a.len());
        body_invariant!(sorted_sublist(result@, 0, result.len() as int));
        body_invariant!(unique_seq(result@, 0, result.len() as int));
        body_invariant!(forall|k: int, l: int| 
            (#[trigger] result@[k], #[trigger] result@[l]) 
            0 <= k && k < l && l < result.len() as int ==> result@[k] < result@[l]);
        body_invariant!(forall|j: int| 
            0 <= j && j < result.len() as int ==> 
            contains_leq(a@, result@[j], i as int, a.len() as int));
        body_invariant!(forall|val: i32| 
            contains_leq(a@, val, i as int, a.len() as int) ==>
            contains_leq(result@, val, 0, result.len() as int));
            
        let current = a[i];
        let mut should_add = true;
        let mut j: usize = 0;
        
        while j < result.len() {
            body_invariant!(0 <= j && j <= result.len());
            body_invariant!(should_add == 
                (forall|k: int| 0 <= k && k < j as int ==> result@[k] != current));
            
            if result[j] == current {
                should_add = false;
                break;
            }
            j += 1;
        }
        
        if should_add {
            let mut k: usize = 0;
            
            while k < result.len() && result[k] < current {
                body_invariant!(0 <= k && k <= result.len());
                body_invariant!(forall|l: int| 0 <= l && l < k as int ==> result@[l] < current);
                k += 1;
            }
            
            result.insert(k, current);
            proof {
                unique_seq_subrange(result@, 0, result.len() as int - 1, result.len() as int);
                sorted_sublist_transitive(result@, 0, k as int, result.len() as int);
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}