use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_list: Vec<i32>)
    // All numbers in the output are even and exist in the input 
    ensures forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == even_list[i],
    // All even numbers in the input are in the output
    ensures forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> exists|j: int| 0 <= j < even_list.len() && even_list[j] == arr[i]
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|k: int|
                0 <= k && k < v@.len() ==>
                    is_even(v@[k] as int)
                    && exists|j: int|
                        0 <= j && j < arr@.len() && j <= i as int && #[trigger] (arr@[j] == v@[k]),
            forall|j: int|
                0 <= j && j < i as int && is_even(arr@[j] as int)
                    ==> exists|k: int| 0 <= k && k < v@.len() && #[trigger] (v@[k] == arr@[j])
    {
        let idx = i;
        let x = arr[idx];
        i = i + 1;
        if is_even(x as int) {
            let old_v = v@;
            v.push(x);
            proof {
                assert(v@.len() == old_v.len() + 1);
                let kk: int = old_v.len();
                assert(0 <= kk && kk < v@.len());
                assert(v@[kk] == x);
                assert(is_even(v@[kk] as int));

                // establish facts about idx within arr@
                assert(arr@.len() == arr.len() as int);
                assert(idx < arr.len());
                let j_w: int = idx as int;
                assert(0 <= j_w && j_w < arr@.len());
                assert(arr@[j_w] == arr[idx]);
                assert(arr[idx] == x);
                assert(arr@[j_w] == x);

                // j_w = idx <= i - 1 < i, hence j_w <= i
                assert(j_w <= i as int);

                // For the newly appended element (k = kk), provide witness j = j_w
                assert(exists|j: int| 0 <= j && j < arr@.len() && j <= i as int && #[trigger] (arr@[j] == v@[kk])) by {
                    let j = j_w;
                    assert(0 <= j && j < arr@.len());
                    assert(j <= i as int);
                    assert(arr@[j] == x);
                    assert(v@[kk] == x);
                };

                // For the second invariant, for the new j = j_w when x is even, provide witness k = kk
                assert(exists|k: int| 0 <= k && k < v@.len() && #[trigger] (v@[k] == arr@[j_w])) by {
                    let k = kk;
                    assert(0 <= k && k < v@.len());
                    assert(v@[k] == x);
                    assert(arr@[j_w] == x);
                };
            }
        }
    }
    v
}
// </vc-code>

fn main() {
}

}