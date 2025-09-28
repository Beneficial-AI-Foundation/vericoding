use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_order_preservation(arr: Seq<i32>, even_numbers: Seq<i32>, new_val: i32, i: int)
    requires
        0 <= i < arr.len(),
        arr[i] == new_val,
        new_val % 2 == 0,
        forall|k: int, l: int| 0 <= k < l < even_numbers.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr.len() && 
            #[trigger] even_numbers[k] == #[trigger] arr[n] && 
            #[trigger] even_numbers[l] == #[trigger] arr[m],
        forall|x: i32| even_numbers.contains(x) ==> 
            exists|j: int| 0 <= j < i && arr[j] == x,
    ensures
        forall|k: int, l: int| 0 <= k < l < even_numbers.push(new_val).len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr.len() && 
            #[trigger] even_numbers.push(new_val)[k] == #[trigger] arr[n] && 
            #[trigger] even_numbers.push(new_val)[l] == #[trigger] arr[m],
{
    let updated = even_numbers.push(new_val);
    assert forall|k: int, l: int| 0 <= k < l < updated.len() implies
        exists|n: int, m: int| 0 <= n < m < arr.len() && 
        #[trigger] updated[k] == #[trigger] arr[n] && 
        #[trigger] updated[l] == #[trigger] arr[m]
    by {
        if l == even_numbers.len() {
            assert(updated[l] == new_val);
            assert(updated[l] == arr[i]);
            
            if k < even_numbers.len() {
                assert(updated[k] == even_numbers[k]);
                let j = choose|j: int| 0 <= j < i && arr[j] == even_numbers[k];
                assert(j < i);
                assert(updated[k] == arr[j]);
                assert(updated[l] == arr[i]);
                assert(0 <= j < i < arr.len());
            }
        } else {
            assert(k < even_numbers.len());
            assert(l < even_numbers.len());
            assert(updated[k] == even_numbers[k]);
            assert(updated[l] == even_numbers[l]);
            let (n, m) = choose|n: int, m: int| 0 <= n < m < arr.len() && 
                even_numbers[k] == arr[n] && 
                even_numbers[l] == arr[m];
            assert(updated[k] == arr[n]);
            assert(updated[l] == arr[m]);
        }
    }
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
    let mut even_numbers = Vec::new();
    let arr_len = arr.len();
    
    for i in 0..arr_len
        invariant
            even_numbers@.len() <= i,
            0 <= i <= arr_len,
            forall|x: i32| #![auto] 0 <= i as int <= arr@.len() && arr@.subrange(0, i as int).contains(x) && x % 2 == 0 ==> 
                even_numbers@.contains(x),
            forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x),
            forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0,
            forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
                exists|n: int, m: int| 0 <= n < m < arr@.len() && 
                #[trigger] even_numbers@[k] == #[trigger] arr@[n] && 
                #[trigger] even_numbers@[l] == #[trigger] arr@[m],
            forall|x: i32| even_numbers@.contains(x) ==> 
                exists|j: int| 0 <= j < i as int && 0 <= j < arr@.len() && arr@[j] == x,
    {
        if arr[i] % 2 == 0 {
            proof {
                assert(0 <= i < arr@.len());
                assert(arr@[i as int] == arr[i]);
                lemma_order_preservation(arr@, even_numbers@, arr[i], i as int);
            }
            even_numbers.push(arr[i]);
        }
    }
    
    assert forall|x: i32| arr@.contains(x) && x % 2 == 0 implies even_numbers@.contains(x) by {
        assert(arr@.subrange(0, arr_len as int) =~= arr@);
    }
    
    even_numbers
}
// </vc-code>

fn main() {
}

}