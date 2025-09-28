use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
spec fn seq_contains<T>(s: Seq<T>, elem: T) -> bool 
    where T: PartialEq
{
    exists|i: int| 0 <= i < s.len() && s[i] == elem
}

proof fn seq_lemma_push_contains<T>(s: Seq<T>, x: T, y: T) 
    ensures 
        seq_contains(s.push(x), y) <==> (x == y || seq_contains(s, y))
{
}

spec fn seq_to_vec<T>(s: Seq<T>) -> Vec<T> {
    Vec::new()
}

spec fn vec_to_seq<T>(v: Vec<T>) -> Seq<T> {
    Seq::empty()
}

proof fn push_preserves_invariant<T>(s: Seq<T>, x: T)
    ensures forall|y: T| seq_contains(s.push(x), y) <==> (x == y || seq_contains(s, y))
{
}

proof fn monotonic_index_invariant(prev_index: int, curr_index: int, arr_len: int)
    requires
        0 <= prev_index <= arr_len,
        prev_index <= curr_index <= arr_len
    ensures
        0 <= curr_index <= arr_len
{
}

proof fn push_preserves_even_invariant(arr: Seq<i32>, s: Seq<i32>, x: i32)
    requires
        forall|i: int| 0 <= i < s.len() ==> is_even(s[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == s[i],
        is_even(x as int),
        exists|j: int| 0 <= j < arr.len() && arr[j] == x
    ensures
        forall|i: int| 0 <= i < s.push(x).len() ==> is_even(s.push(x)[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == s.push(x)[i]
{
}

proof fn push_preserves_coverage(arr: Seq<i32>, s: Seq<i32>, x: i32, index: int)
    requires
        forall|j: int| 0 <= j < index && is_even(arr[j] as int) ==> seq_contains(s, arr[j]),
        0 <= index < arr.len(),
        x == arr[index],
        is_even(x as int)
    ensures
        forall|j: int| 0 <= j <= index && is_even(arr[j] as int) ==> seq_contains(s.push(x), arr[j])
{
    assert forall|j: int| 0 <= j <= index && is_even(arr[j] as int) implies seq_contains(s.push(x), arr[j]) by {
        if j == index {
            assert(s.push(x)[s.len()] == x);
            assert(x == arr[j]);
        } else {
            assert(j < index);
            assert(seq_contains(s, arr[j]));
            push_preserves_invariant(s, x, arr[j]);
        }
    }
}
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
    let mut even_list = Vec::new();
    let mut index: usize = 0;
    
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < even_list@.len() ==> is_even(even_list@[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == even_list@[i],
            forall|j: int| 0 <= j < index && is_even(arr[j] as int) ==> seq_contains(even_list@, arr[j])
    {
        let element = arr[index];
        if element % 2 == 0 {
            proof {
                let old_seq = even_list@;
            }
            even_list.push(element);
            proof {
                let new_seq = even_list@;
                
                assert forall|i: int| 0 <= i < new_seq.len() implies is_even(new_seq[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == new_seq[i] by {
                    if i == new_seq.len() - 1 {
                        assert(new_seq[i] == element);
                        assert(is_even(element as int));
                        assert(arr[index] == element);
                    } else {
                        assert(old_seq[i] == new_seq[i]);
                    }
                }
                
                push_preserves_coverage(arr, old_seq, element, index as int);
            }
        }
        index += 1;
        proof {
            monotonic_index_invariant((index - 1) as int, index as int, arr.len() as int);
        }
    }
    even_list
}
// </vc-code>

fn main() {
}

}