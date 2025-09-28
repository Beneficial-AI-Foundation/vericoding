use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_order_preserved(indices: Seq<nat>, result: Seq<i32>, arr: Seq<i32>)
    requires
        indices.len() == result.len(),
        forall |k: int| 0 <= k < result.len() ==> 
            0 <= (indices[k] as int) < arr.len() && arr@[indices[k] as int] == result@[k],
        forall |k: int, l: int| 0 <= k < l < result.len() ==> indices[k] < indices[l]
    ensures
        forall |k: int, l: int| 0 <= k < l < result.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr.len() && 
            result@[k] == arr@[n] && 
            result@[l] == arr@[m]
{
    assert(forall |k: int, l: int| 0 <= k < l < result.len() ==> 
        {
            let n = indices[k] as int;
            let m = indices[l] as int;
            0 <= n < arr.len() && 0 <= m < arr.len() && n < m && 
            arr@[n] == result@[k] && arr@[m] == result@[l]
        });
}
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_numbers: Vec<i32>)
    ensures 
        (forall|x: i32| arr@.contains(x) && x % 2 == 0 ==> even_numbers@.contains(x)) &&
        (forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x)) &&
        (forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0) &&
        (forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr@.len() && 
            #[trigger] even_numbers@[k] == #[trigger] arr@[n] && 
            #[trigger] even_numbers@[l] == #[trigger] arr@[m])
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let ghost indices: Seq<nat> = Seq::empty();

    let mut i: usize = 0;
    let len = arr.len();
    while i < len
        invariant
            0 <= (i as
// </vc-code>

fn main() {
}

}