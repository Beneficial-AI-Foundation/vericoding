use vstd::prelude::*;

verus! {

/**
 * Find odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
// Helper lemma to maintain that all elements added so far are odd and from the input
proof fn lemma_push_maintains_invariant(
    arr: Seq<i32>,
    odd_list: Seq<i32>,
    val: i32,
)
    requires
        forall|j: int| 0 <= j < odd_list.len() ==> is_odd(odd_list[j] as int) && arr.contains(odd_list[j]),
        is_odd(val as int),
        arr.contains(val),
    ensures
        forall|j: int| 0 <= j < odd_list.push(val).len() ==> 
            is_odd(odd_list.push(val)[j] as int) && arr.contains(odd_list.push(val)[j]),
{
    assert forall|j: int| 0 <= j < odd_list.push(val).len() implies 
        is_odd(odd_list.push(val)[j] as int) && arr.contains(odd_list.push(val)[j]) by {
        if j < odd_list.len() {
            assert(odd_list.push(val)[j] == odd_list[j]);
        } else {
            assert(j == odd_list.len());
            assert(odd_list.push(val)[j] == val);
        }
    }
}

// Helper lemma showing that pushing preserves containment
proof fn lemma_push_preserves_contains(s: Seq<i32>, val: i32, elem: i32)
    requires s.contains(elem),
    ensures s.push(val).contains(elem),
{
    let new_s = s.push(val);
    assert(new_s.len() == s.len() + 1);
    // Use proper syntax for exists
    assert(exists|k: int| 0 <= k < s.len() && s[k] == elem);
    let k_witness = choose|k: int| 0 <= k < s.len() && s[k] == elem;
    assert(0 <= k_witness < new_s.len());
    assert(new_s[k_witness] == elem);
}
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &[i32]) -> (odd_list: Vec<i32>)
    // All numbers in the output are odd and exist in the input 
    ensures forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i] as int) && arr@.contains(odd_list[i])
    // All odd numbers in the input are in the output
    ensures forall|i: int| 0 <= i < arr.len() && is_odd(arr[i] as int) ==> odd_list@.contains(arr[i])
// </vc-spec>
// <vc-code>
{
    let mut odd_list: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            // All elements in odd_list are odd and from arr
            forall|j: int| 0 <= j < odd_list.len() ==> 
                is_odd(odd_list[j] as int) && arr@.contains(odd_list[j]),
            // All odd numbers before index i are in odd_list
            forall|j: int| 0 <= j < i && is_odd(arr[j] as int) ==> 
                odd_list@.contains(arr[j]),
    {
        if arr[i] % 2 == 1 {
            let old_odd_list = odd_list@;
            
            proof {
                lemma_push_maintains_invariant(arr@, old_odd_list, arr[i]);
                
                // Prove that all previously seen odd numbers are still in the list
                assert forall|j: int| 0 <= j < i && is_odd(arr[j] as int) implies 
                    old_odd_list.push(arr[i]).contains(arr[j]) by {
                    if old_odd_list.contains(arr[j]) {
                        lemma_push_preserves_contains(old_odd_list, arr[i], arr[j]);
                    }
                }
            }
            
            odd_list.push(arr[i]);
            
            assert(odd_list@ =~= old_odd_list.push(arr[i]));
            assert(is_odd(arr[i] as int));
            assert(odd_list@.contains(arr[i]));
        }
        i = i + 1;
    }

    odd_list
}
// </vc-code>

fn main() {}

}