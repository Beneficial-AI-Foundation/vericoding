use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// <vc-code>
{
    let a_seq = a@;
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len() 
        invariant
            0 <= i as int && i as int <= a.len() as int,
            forall|k:int, l:int| 0 <= k < l < result.len() ==> result@[k] != result@[l],
            forall|x:i32| result@.contains(x) ==> exists|j:int| 0 <= j < i as int && a_seq[j] == x,
            forall|k:int| 0 <= k < i as int ==> result@.contains(a_seq[k])
    {
        let elem = a[i];
        if !result@.contains(elem) {
           result.push(elem);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {
}

}