use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to check if a sequence contains an element up to a certain index
spec fn contains_up_to(s: Seq<int>, x: int, up_to: nat) -> bool
    decreases up_to,
{
    if up_to == 0 {
        false
    } else {
        s[up_to - 1] == x || contains_up_to(s, x, (up_to - 1) as nat)
    }
}

// Lemma: if contains_up_to is true, then the element exists at some index
proof fn contains_up_to_implies_exists(s: Seq<int>, x: int, up_to: nat)
    requires
        up_to <= s.len(),
        contains_up_to(s, x, up_to),
    ensures
        exists|j: int| 0 <= j < up_to && s[j] == x,
    decreases up_to,
{
    if up_to > 0 {
        if s[up_to - 1] == x {
            assert(s[up_to - 1] == x);
        } else {
            contains_up_to_implies_exists(s, x, (up_to - 1) as nat);
        }
    }
}

// Lemma: if an element exists at some index, contains_up_to is true
proof fn exists_implies_contains_up_to(s: Seq<int>, x: int, up_to: nat, idx: int)
    requires
        up_to <= s.len(),
        0 <= idx < up_to,
        s[idx] == x,
    ensures
        contains_up_to(s, x, up_to),
    decreases up_to,
{
    if up_to > 0 {
        if idx == up_to - 1 {
            assert(s[up_to - 1] == x);
        } else {
            exists_implies_contains_up_to(s, x, (up_to - 1) as nat, idx);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j),
// </vc-spec>
// <vc-code>
{
    let mut diff: Vec<int> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|x: int| #[trigger] diff@.contains(x) ==> 
                (a.contains(x) && !b.contains(x)),
            forall|x: int| (a.contains(x) && !b.contains(x)) ==> 
                (diff@.contains(x) || exists|j: int| i <= j < a.len() && a[j] == x),
            forall|j1: int, j2: int| 0 <= j1 < j2 < diff@.len() ==> 
                diff@[j1] != diff@[j2],
            forall|j: int| 0 <= j < diff@.len() ==> 
                !contains_up_to(diff@, diff@[j], j as nat),
    {
        let elem = a@[i as int];
        
        // Check if elem is in b
        let mut in_b = false;
        let mut j: usize = 0;
        while j < b.len()
            invariant
                j <= b.len(),
                in_b <==> exists|k: int| 0 <= k < j && b[k] == elem,
        {
            if b@[j as int] == elem {
                in_b = true;
            }
            j = j + 1;
        }
        assert(in_b <==> b.contains(elem));
        
        if !in_b {
            // Check if elem is already in diff
            let mut already_in_diff = false;
            let mut k: usize = 0;
            while k < diff.len()
                invariant
                    k <= diff.len(),
                    already_in_diff <==> contains_up_to(diff@, elem, k as nat),
            {
                if diff[k] == elem {
                    already_in_diff = true;
                    proof {
                        exists_implies_contains_up_to(diff@, elem, (k + 1) as nat, k as int);
                    }
                }
                k = k + 1;
            }
            assert(already_in_diff <==> contains_up_to(diff@, elem, diff@.len() as nat));
            
            if !already_in_diff {
                proof {
                    // Prove that adding elem maintains uniqueness
                    assert forall|j: int| 0 <= j < diff@.len() implies diff@[j] != elem by {
                        if diff@[j] == elem {
                            exists_implies_contains_up_to(diff@, elem, diff@.len() as nat, j);
                            assert(contains_up_to(diff@, elem, diff@.len() as nat));
                            assert(false);
                        }
                    }
                }
                diff.push(elem);
            }
        }
        
        i = i + 1;
    }
    
    // Final proof that all elements from a not in b are in diff
    proof {
        assert forall|x: int| (a.contains(x) && !b.contains(x)) implies diff@.contains(x) by {
            if a.contains(x) && !b.contains(x) {
                let a_idx = choose|j: int| 0 <= j < a.len() && a[j] == x;
                assert(exists|j: int| 0 <= j < a.len() && a[j] == x);
                assert(diff@.contains(x) || exists|j: int| i <= j < a.len() && a[j] == x);
                assert(i == a.len());
                assert(diff@.contains(x));
            }
        }
    }
    
    diff@
}
// </vc-code>

fn main() {}

}