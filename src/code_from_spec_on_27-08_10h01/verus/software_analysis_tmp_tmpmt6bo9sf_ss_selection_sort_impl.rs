use vstd::prelude::*;

verus! {

fn find_min_index(a: &Vec<i32>, s: usize, e: usize) -> (min_i: usize)
    requires 
        a.len() > 0,
        s < a.len(),
        e <= a.len(),
        e > s,
    ensures 
        min_i >= s,
        min_i < e,
        forall|k: int| s <= k < e ==> a[min_i as int] <= a[k],
{
    assume(false);
    s
}

spec fn is_sorted(ss: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < ss.len() ==> ss[i] <= ss[j]
}

spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool
    decreases a.len(), b.len()
{
    a.len() == b.len() && 
    ((a.len() == 0 && b.len() == 0) ||  
     (exists|i: int, j: int| {
        0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j] && 
        is_permutation(
            a.subrange(0, i) + {if i < a.len() { a.subrange(i + 1, a.len() as int) } else { seq![] }},
            b.subrange(0, j) + {if j < b.len() { b.subrange(j + 1, b.len() as int) } else { seq![] }}
        )
     }))
}

spec fn is_permutation2(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.to_multiset() == b.to_multiset()
}

// <vc-helpers>
proof fn multiset_update_preserves_permutation<T>(v: Seq<T>, i: int, j: int)
    requires 
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures 
        v.update(i, v[j]).update(j, v[i]).to_multiset() == v.to_multiset()
{
    let v1 = v.update(i, v[j]);
    let v2 = v1.update(j, v[i]);
    
    assert(v2.to_multiset().count(v[i]) == v.to_multiset().count(v[i]));
    assert(v2.to_multiset().count(v[j]) == v.to_multiset().count(v[j]));
    
    assert forall|x: T| #[trigger] v2.to_multiset().count(x) == v.to_multiset().count(x) by {
        if x == v[i] && x == v[j] {
        } else if x == v[i] {
        } else if x == v[j] {
        } else {
        }
    };
}

proof fn sorted_subrange_remains_sorted(v: Seq<i32>, start: int, end: int)
    requires 
        is_sorted(v),
        0 <= start <= end <= v.len()
    ensures 
        is_sorted(v.subrange(start, end))
{
}

proof fn sorted_after_min_swap(v: Seq<i32>, pos: int, min_idx: int)
    requires 
        0 <= pos < v.len(),
        pos <= min_idx < v.len(),
        forall|k: int| pos <= k < v.len() ==> v[min_idx] <= v[k],
        is_sorted(v.subrange(0, pos))
    ensures 
        is_sorted(v.update(pos, v[min_idx]).update(min_idx, v[pos]).subrange(0, pos + 1))
{
    let new_v = v.update(pos, v[min_idx]).update(min_idx, v[pos]);
    
    if pos > 0 {
        assert forall|i: int, j: int| 0 <= i <= j < pos implies new_v[i] <= new_v[j] by {
            assert(new_v.subrange(0, pos) =~= v.subrange(0, pos));
        };
        
        assert forall|i: int| 0 <= i < pos implies new_v[i] <= new_v[pos] by {
            assert(new_v[i] == v[i]);
            assert(new_v[pos] == v[min_idx]);
            assert(v[min_idx] <= v[pos]);
        };
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn selection_sort(ns: &mut Vec<i32>) 
    requires old(ns).len() >= 0
    ensures 
        is_sorted(ns@),
        is_permutation2(old(ns)@, ns@),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    
    while i < ns.len()
        invariant 
            0 <= i <= ns.len(),
            is_sorted(ns@.subrange(0, i as int)),
            is_permutation2(old(ns)@, ns@),
            forall|a: int, b: int| 0 <= a < i && i <= b < ns.len() ==> ns@[a] <= ns@[b]
    {
        if i < ns.len() {
            let min_idx = find_min_index(ns, i, ns.len());
            
            proof {
                multiset_update_preserves_permutation(ns@, i as int, min_idx as int);
            }
            
            let ghost temp = ns@[i as int];
            ns.set(i, ns[min_idx as int]);
            ns.set(min_idx, temp);
            
            proof {
                let old_ns_loop = old(ns)@;
                sorted_after_min_swap(old(ns)@, i as int, min_idx as int);
                
                assert forall|a: int, b: int| 0 <= a < (i + 1) && (i + 1) <= b < ns.len() implies ns@[a] <= ns@[b] by {
                    if a < i {
                    } else {
                        assert(a == i);
                        assert(ns@[a] == old(ns)@[min_idx as int]);
                    }
                };
            }
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}

}