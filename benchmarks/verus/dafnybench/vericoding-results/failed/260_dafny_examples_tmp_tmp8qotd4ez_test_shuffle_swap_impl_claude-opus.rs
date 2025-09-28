use vstd::prelude::*;

verus! {

spec fn set_of_seq<T>(s: Seq<T>) -> Set<T> {
    Set::new(|x: T| s.contains(x))
}

// <vc-helpers>
// Helper lemma to prove that swapping two elements preserves the multiset
proof fn swap_preserves_multiset<T>(s: Seq<T>, i: int, j: int, result: Seq<T>)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        result.len() == s.len(),
        result[i] == s[j],
        result[j] == s[i],
        forall|k: int| 0 <= k < s.len() && k != i && k != j ==> result[k] == s[k],
    ensures
        result.to_multiset() == s.to_multiset(),
{
    assert forall|x: T| #[trigger] result.to_multiset().count(x) == s.to_multiset().count(x) by {
        let result_count = result.filter(|y: T| y == x).len();
        let s_count = s.filter(|y: T| y == x).len();
        
        if i == j {
            assert(result =~= s);
            assert(result_count == s_count);
        } else {
            // Count occurrences in both sequences
            assert(result_count == s_count);
        }
    }
    assert(result.to_multiset() =~= s.to_multiset());
}
// </vc-helpers>

// <vc-spec>
fn swap<T>(a: &mut Vec<T>, i: usize, j: usize)
    requires 
        i < old(a).len(),
        j < old(a).len(),
    ensures
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|m: int| 0 <= m < a.len() && m != i && m != j ==> a[m] == old(a)[m],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let ghost old_a = a@;
    
    // Manually swap elements using a temporary variable
    let temp = a[i];
    a.set(i, a[j]);
    a.set(j, temp);
    
    assert(a@[i as int] == old_a[j as int]);
    assert(a@[j as int] == old_a[i as int]);
    assert(forall|m: int| 0 <= m < a@.len() && m != i as int && m != j as int ==> a@[m] == old_a[m]);
    
    // Prove multiset preservation
    proof {
        swap_preserves_multiset(old_a, i as int, j as int, a@);
    }
}
// </vc-code>

fn main() {}

}