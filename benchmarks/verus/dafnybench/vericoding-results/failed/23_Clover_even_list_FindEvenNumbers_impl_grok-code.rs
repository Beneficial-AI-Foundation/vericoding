use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_filtered_preserves_order(s: Seq<i32>)
    ensures
        forall|k: int, l: int| 0 <= k < l < s.filter(|x: i32| x % 2 == 0).len() ==>
            exists|n: int, m: int| 0 <= n < m < s.len() &&
            #[trigger] (s.filter(|x: i32| x % 2 == 0)@[k]) == #[trigger] s@[n] &&
            #[trigger] (s.filter(|x: i32| x % 2 == 0)@[l]) == #[trigger] s@[m];
{
    if s.len() == 0 {
    } else {
        lemma_filtered_preserves_order(s.subrange(0, s.len() - 1));
        proof {
            let filtered_old = s.subrange(0, s.len() - 1).filter(|x: i32| x % 2 == 0);
            let filtered = s.filter(|x: i32| x % 2 == 0);
            let m = s.len() - 1;
            if s@[m] % 2 == 0 {
                assert(filtered == filtered_old.push(s@[m]));
                // Assert that filtered_old's indices map to old sequence
                let ghost last_index = filtered_old.len();
                // For pairs where l < last_index, use inductive hypothesis
                assert(forall|k: int, l: int| 0 <= k < l < last_index ==>
                    exists|n: int, m_: int| 0 <= n < m_ <= s.len() - 2 &&
                    #[trigger] filtered@[k] == #[trigger] s@[n] &&
                    #[trigger] filtered@[l] == #[trigger] s@[m_]);
                // For pairs where k < last_index and l == last_index
                assert(forall|k: int| 0 <= k < last_index ==> 
                    exists|n: int| 0 <= n < m &&
                    #[trigger] filtered@[k] == #[trigger] s@[n]);
                // l = last_index maps to s@[m]
                assert(filtered@[last_index] == s@[m]);
                // Combine to assert the overall forall
                assert(forall|k: int, l: int| 0 <= k < l < filtered.len() ==>
                    exists|n: int, m_: int| 0 <= n < m_ < s.len() &&
                    #[trigger] filtered@[k] == #[trigger] s@[n] &&
                    #[trigger] filtered@[l] == #[trigger] s@[m_]);
            } else {
                assert(filtered == filtered_old);
                // Direct from inductive hypothesis
                assert(forall|k: int, l: int| 0 <= k < l < filtered.len() ==>
                    exists|n: int, m_: int| 0 <= n < m_ < m &&
                    #[trigger] filtered@[k] == #[trigger] s@[n] &&
                    #[trigger] filtered@[l] == #[trigger] s@[m_]);
            }
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
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr@.len(),
            even_numbers@ == arr@[0..i].filter(|x: i32| x % 2 == 0)
    {
        if arr@[i] % 2 == 0 {
            even_numbers.push(arr@[i]);
        }
        i += 1;
        proof {
            assert(arr@[0..i] == arr@[0..old(i)].push(arr@[old(i)]));
            if arr@[old(i)] % 2 == 0 {
                assert(even_numbers@ == old(even_numbers)@.push(arr@[old(i)]));
            } else {
                assert(even_numbers@ == old(even_numbers)@);
            }
            assert(even_numbers@ == arr@[0..i].filter(|x: i32| x % 2 == 0));
        }
    }
    proof {
        lemma_filtered_preserves_order(arr@);
        assert(even_numbers@ == arr@.filter(|x: i32| x % 2 == 0));
        assert(forall|x: i32| arr@.contains(x) && x % 2 == 0 ==> even_numbers@.contains(x));
        assert(forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x));
        assert(forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0);
        // Prove the order preservation via the lemma's ensures
        assert(forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr@.len() && 
            #[trigger] even_numbers@[k] == #[trigger] arr@[n] && 
            #[trigger] even_numbers@[l] == #[trigger] arr@[m]);
    }
    even_numbers
}
// </vc-code>

fn main() {
}

}