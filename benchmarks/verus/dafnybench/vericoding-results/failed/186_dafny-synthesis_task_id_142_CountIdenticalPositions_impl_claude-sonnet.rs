use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_set_cardinality_bound(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    requires
        a.len() == b.len() && b.len() == c.len(),
    ensures
        Set::<int>::new(|i: int| 0 <= i < a.len() && a@[i] == b@[i] && b@[i] == c@[i]).len() <= a.len(),
{
    let s = Set::<int>::new(|i: int| 0 <= i < a.len() && a@[i] == b@[i] && b@[i] == c@[i]);
    let range_set = Set::<int>::new(|i: int| 0 <= i < a.len());
    
    assert forall |i: int| s.contains(i) implies range_set.contains(i) by {
        if s.contains(i) {
            assert(0 <= i < a.len() && a@[i] == b@[i] && b@[i] == c@[i]);
        }
    }
    
    assert(s.subset_of(range_set));
    assert(range_set.len() == a.len());
}

proof fn lemma_count_preservation(a: Seq<int>, b: Seq<int>, c: Seq<int>, count: usize, i: usize)
    requires
        a.len() == b.len() && b.len() == c.len(),
        i <= a.len(),
        count == Set::<int>::new(|j: int| 0 <= j < i && a@[j] == b@[j] && b@[j] == c@[j]).len(),
    ensures
        i < a.len() ==> {
            let new_count = if a@[i as int] == b@[i as int] && b@[i as int] == c@[i as int] {
                count + 1
            } else {
                count as int
            };
            new_count == Set::<int>::new(|j: int| 0 <= j < (i + 1) && a@[j] == b@[j] && b@[j] == c@[j]).len()
        },
{
    if i < a.len() {
        let old_set = Set::<int>::new(|j: int| 0 <= j < i && a@[j] == b@[j] && b@[j] == c@[j]);
        let new_set = Set::<int>::new(|j: int| 0 <= j < (i + 1) && a@[j] == b@[j] && b@[j] == c@[j]);
        
        if a@[i as int] == b@[i as int] && b@[i as int] == c@[i as int] {
            assert(new_set == old_set.insert(i as int));
            assert(!old_set.contains(i as int));
            assert(new_set.len() == old_set.len() + 1);
        } else {
            assert forall |j: int| old_set.contains(j) implies new_set.contains(j) by {
                if old_set.contains(j) {
                    assert(0 <= j < i && a@[j] == b@[j] && b@[j] == c@[j]);
                    assert(0 <= j < (i + 1) && a@[j] == b@[j] && b@[j] == c@[j]);
                }
            }
            
            assert forall |j: int| new_set.contains(j) implies old_set.contains(j) by {
                if new_set.contains(j) {
                    assert(0 <= j < (i + 1) && a@[j] == b@[j] && b@[j] == c@[j]);
                    if j == i {
                        assert(a@[i as int] == b@[i as int] && b@[i as int] == c@[i as int]);
                        assert(false);
                    }
                    assert(j < i);
                    assert(0 <= j < i && a@[j] == b@[j] && b@[j] == c@[j]);
                }
            }
            
            assert(old_set =~= new_set);
            assert(new_set.len() == old_set.len());
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count_identical_positions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: usize)
    requires
        a.len() == b.len() && b.len() == c.len(),
    ensures
        count >= 0,
        count == Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len(),
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_set_cardinality_bound(a, b, c);
    }
    
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            a.len() == b.len() && b.len() == c.len(),
            i <= a.len(),
            count == Set::<int>::new(|j: int| 0 <= j < i && a@[j] == b@[j] && b@[j] == c@[j]).len(),
    {
        proof {
            lemma_count_preservation(a, b, c, count, i);
        }
        
        let ghost idx = i as int;
        let condition = proof {
            a@[idx] == b@[idx] && b@[idx] == c@[idx]
        };
        
        if condition {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == a.len());
        assert(count == Set::<int>::new(|j: int| 0 <= j < a.len() && a@[j] == b@[j] && b@[j] == c@[j]).len());
    }
    
    count
}
// </vc-code>

fn main() {
}

}