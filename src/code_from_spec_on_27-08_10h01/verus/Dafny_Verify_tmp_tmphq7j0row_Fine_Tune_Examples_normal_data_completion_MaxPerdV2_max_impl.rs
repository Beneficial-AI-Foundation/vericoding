use vstd::prelude::*;

verus! {

spec fn contains(v: i32, a: Seq<i32>, n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j] == v
}

spec fn upper_bound(v: i32, a: Seq<i32>, n: int) -> bool {
    forall|j: int| 0 <= j < n ==> a[j] <= v
}

spec fn is_max(m: i32, a: Seq<i32>, n: int) -> bool {
    contains(m, a, n) && upper_bound(m, a, n)
}

// <vc-helpers>
proof fn lemma_max_invariant_maintains_properties(a: Seq<i32>, current_max: i32, i: int, n: int)
    requires 
        0 < i <= n,
        contains(current_max, a, i - 1),
        upper_bound(current_max, a, i - 1),
    ensures 
        contains(if a[i - 1] > current_max { a[i - 1] } else { current_max }, a, i),
        upper_bound(if a[i - 1] > current_max { a[i - 1] } else { current_max }, a, i),
{
    let new_max = if a[i - 1] > current_max { a[i - 1] } else { current_max };
    
    // Prove contains property
    if a[i - 1] > current_max {
        // new_max is a[i - 1], which is at position i - 1
        assert(a[i - 1] == new_max);
        assert(0 <= i - 1 < i);
    } else {
        // new_max is current_max, which already exists in a[0..i-1]
        assert(contains(current_max, a, i - 1));
        assert(new_max == current_max);
        // Since current_max exists in a[0..i-1], it also exists in a[0..i]
        assert(contains(new_max, a, i));
    }
    
    // Prove upper_bound property
    assert forall|j: int| 0 <= j < i implies a[j] <= new_max by {
        if j < i - 1 {
            assert(a[j] <= current_max);
            assert(current_max <= new_max);
        } else if j == i - 1 {
            if a[i - 1] > current_max {
                assert(new_max == a[i - 1]);
                assert(a[j] == a[i - 1] == new_max);
            } else {
                assert(new_max == current_max);
                assert(a[j] == a[i - 1] <= current_max == new_max);
            }
        }
    };
}

proof fn lemma_final_max_extends_to_n(a: Seq<i32>, final_max: i32, n: int)
    requires 
        0 < n,
        contains(final_max, a, n),
        upper_bound(final_max, a, n),
    ensures is_max(final_max, a, n),
{
    // This follows directly from the definition of is_max
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires 0 < n <= a.len(),
    ensures is_max(max, a@, n as int),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut max_val = a[0];
    let mut i = 1;
    
    while i < n
        invariant 
            0 < i <= n,
            i <= a.len(),
            n <= a.len(),
            contains(max_val, a@, i as int),
            upper_bound(max_val, a@, i as int),
        decreases n - i,
    {
        let old_max_val = max_val;
        
        if a[i] > max_val {
            max_val = a[i];
        }
        
        i += 1;
        
        proof {
            lemma_max_invariant_maintains_properties(a@, old_max_val, i as int, n as int);
        }
    }
    
    proof {
        lemma_final_max_extends_to_n(a@, max_val, n as int);
    }
    
    max_val
}
// </vc-code>

fn main() {}

}