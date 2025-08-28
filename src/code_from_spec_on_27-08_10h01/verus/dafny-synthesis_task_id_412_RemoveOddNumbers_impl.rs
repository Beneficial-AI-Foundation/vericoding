use vstd::prelude::*;

verus! {

/**
 * Remove odd numbers from an array of numbers
 **/

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
proof fn lemma_contains_push<T>(v: Seq<T>, x: T, y: T)
    ensures
        v.push(x).contains(y) == (v.contains(y) || x == y)
{
}

proof fn lemma_push_index<T>(v: Seq<T>, x: T, i: int)
    requires 0 <= i < v.len()
    ensures v.push(x)[i] == v[i]
{
}

proof fn lemma_push_last<T>(v: Seq<T>, x: T)
    ensures v.push(x)[v.len() as int] == x
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn remove_odd_numbers(arr: &[i32]) -> (even_list: Vec<i32>)
    ensures
        // All numbers in the output are even and exist in the input 
        forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && arr@.contains(even_list[i]),
        // All even numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> even_list@.contains(arr[i])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut even_list = Vec::new();
    
    for i in 0..arr.len()
        invariant
            // All numbers in even_list are even and exist in arr
            forall|j: int| 0 <= j < even_list.len() ==> is_even(even_list[j] as int) && arr@.contains(even_list[j]),
            // All even numbers from arr[0..i] are in even_list
            forall|j: int| 0 <= j < i ==> (is_even(arr[j] as int) ==> even_list@.contains(arr[j]))
    {
        if arr[i] % 2 == 0 {
            proof {
                assert(is_even(arr[i as int] as int));
                let old_even_list = even_list@;
                
                // Prove the first invariant will be maintained
                assert(forall|j: int| 0 <= j < old_even_list.len() ==> is_even(old_even_list[j] as int) && arr@.contains(old_even_list[j]));
                assert(arr@.contains(arr[i as int]));
                
                // After push, the new element is the last one
                lemma_push_last(old_even_list, arr[i as int]);
                
                // All previous elements remain the same
                assert(forall|j: int| 0 <= j < old_even_list.len() ==> 
                    old_even_list.push(arr[i as int])[j] == old_even_list[j]) by {
                    assert forall|j: int| 0 <= j < old_even_list.len() implies 
                        old_even_list.push(arr[i as int])[j] == old_even_list[j] by {
                        lemma_push_index(old_even_list, arr[i as int], j);
                    }
                };
            }
            
            even_list.push(arr[i]);
            
            proof {
                // Prove the second invariant will be maintained
                let new_even_list = even_list@;
                assert(new_even_list.contains(arr[i as int]));
                
                // For all j < i, if arr[j] is even, it was already in the old list
                assert(forall|j: int| 0 <= j < i ==> (is_even(arr[j] as int) ==> 
                    new_even_list.contains(arr[j as int]))) by {
                    assert forall|j: int| 0 <= j < i && is_even(arr[j] as int) implies
                        new_even_list.contains(arr[j as int]) by {
                        lemma_contains_push(new_even_list.drop_last(), arr[i as int], arr[j as int]);
                    }
                };
                
                // For j == i, we just added it
                assert(is_even(arr[i as int] as int) ==> new_even_list.contains(arr[i as int]));
            }
        }
    }
    
    even_list
}
// </vc-code>

fn main() {
}

}