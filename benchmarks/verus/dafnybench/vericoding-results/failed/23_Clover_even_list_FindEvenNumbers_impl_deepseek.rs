use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_contains_index<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.contains(s[i]),
{
}

proof fn lemma_seq_contains_implies_index<A>(s: Seq<A>, x: A)
    requires
        s.contains(x),
    ensures
        exists|i: int| 0 <= i < s.len() && s[i] == x,
{
}

proof fn lemma_vec_contains_elem<A>(v: &Vec<A>, x: A) -> (idx: int)
    requires
        v@.contains(x),
    ensures
        0 <= idx < v@.len() && v@[idx] == x,
{
}

proof fn lemma_ordering_preserved(arr: Seq<i32>, even_numbers: Seq<i32>, k: int, l: int)
    requires
        0 <= k < l < even_numbers.len(),
        (forall|n: int, m: int| 0 <= n < m < arr.len() && arr[n] % 2 == 0 && arr[m] % 2 == 0 ==> 
            exists|p: int, q: int| 0 <= p < q < even_numbers.len() && even_numbers[p] == arr[n] && even_numbers[q] == arr[m]),
    ensures
        exists|n: int, m: int| 0 <= n < m < arr.len() && even_numbers[k] == arr[n] && even_numbers[l] == arr[m],
{
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
    let mut indices = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i as int <= arr.len() as int,
            even_numbers@.len() == indices@.len(),
            (forall|j: int| 0 <= j < even_numbers@.len() ==> even_numbers@[j] % 2 == 0),
            (forall|j: int| 0 <= j < even_numbers@.len() ==> 0 <= indices@[j] < arr.len() as int && even_numbers@[j] == arr[indices@[j] as usize]),
            (forall|j: int, k: int| 0 <= j < k < indices@.len() ==> indices@[j] < indices@[k]),
            (forall|x: i32| x % 2 == 0 && arr@.contains(x) ==> even_numbers@.contains(x)),
    {
        if arr[i] % 2 == 0 {
            even_numbers.push(arr[i]);
            indices.push(i as i32);
            proof {
                assert(even_numbers@.contains(arr[i]));
            }
        }
        i += 1;
    }

    proof {
        assert(forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x));
        assert(forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0);
        
        assert(forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr@.len() && 
            even_numbers@[k] == arr@[n] && 
            even_numbers@[l] == arr@[m]);
    }

    even_numbers
}
// </vc-code>

fn main() {
}

}