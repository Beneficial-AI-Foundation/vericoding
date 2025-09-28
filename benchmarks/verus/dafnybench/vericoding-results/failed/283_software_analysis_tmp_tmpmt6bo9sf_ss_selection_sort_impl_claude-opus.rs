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
proof fn lemma_swap_maintains_permutation(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        is_permutation2(a, a.update(i, a[j]).update(j, a[i])),
{
    let swapped = a.update(i, a[j]).update(j, a[i]);
    assert forall|k: int| 0 <= k < a.len() implies 
        a.to_multiset().count(a[k]) == swapped.to_multiset().count(a[k]) by {
        if k == i {
            assert(swapped[i] == a[j]);
            assert(swapped[j] == a[i]);
        } else if k == j {
            assert(swapped[j] == a[i]);
            assert(swapped[i] == a[j]);
        } else {
            assert(swapped[k] == a[k]);
        }
    }
    assert(a.to_multiset() =~= swapped.to_multiset());
}

proof fn lemma_permutation_transitive(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>)
    requires
        is_permutation2(a, b),
        is_permutation2(b, c),
    ensures
        is_permutation2(a, c),
{
    assert(a.to_multiset() == b.to_multiset());
    assert(b.to_multiset() == c.to_multiset());
    assert(a.to_multiset() == c.to_multiset());
}

proof fn lemma_sorted_subrange_preserved(ns: Seq<i32>, i: int, min_i: int)
    requires
        0 < i <= ns.len(),
        i <= min_i < ns.len(),
        forall|k: int, l: int| 0 <= k < l < i ==> #[trigger] ns[k] <= #[trigger] ns[l],
        forall|k: int| i <= k < ns.len() ==> ns[min_i] <= #[trigger] ns[k],
        forall|k: int| 0 <= k < i ==> #[trigger] ns[k] <= ns[min_i],
    ensures
        forall|k: int, l: int| 0 <= k < l <= i ==> 
            #[trigger] ns.update(i-1, ns[min_i]).update(min_i, ns[i-1])[k] <= 
            #[trigger] ns.update(i-1, ns[min_i]).update(min_i, ns[i-1])[l],
{
    let swapped = ns.update(i-1, ns[min_i]).update(min_i, ns[i-1]);
    assert forall|k: int, l: int| 0 <= k < l <= i implies #[trigger] swapped[k] <= #[trigger] swapped[l] by {
        if l < i {
            if k == i - 1 {
                assert(swapped[k] == ns[min_i]);
                if l == min_i {
                    assert(swapped[l] == ns[i-1]);
                    assert(ns[min_i] <= ns[i-1]);
                } else {
                    assert(swapped[l] == ns[l]);
                    assert(ns[min_i] <= ns[l]);
                }
            } else if l == i - 1 {
                assert(swapped[l] == ns[min_i]);
                if k == min_i {
                    assert(swapped[k] == ns[i-1]);
                    assert(ns[i-1] <= ns[min_i]);
                } else {
                    assert(swapped[k] == ns[k]);
                    assert(ns[k] <= ns[min_i]);
                }
            } else {
                if k == min_i {
                    assert(swapped[k] == ns[i-1]);
                    assert(swapped[l] == ns[l]);
                    assert(ns[i-1] <= ns[l]);
                } else if l == min_i {
                    assert(swapped[k] == ns[k]);
                    assert(swapped[l] == ns[i-1]);
                    assert(ns[k] <= ns[i-1]);
                } else {
                    assert(swapped[k] == ns[k]);
                    assert(swapped[l] == ns[l]);
                    assert(ns[k] <= ns[l]);
                }
            }
        } else {
            assert(l == i);
            assert(swapped[l] == swapped[i-1]);
            assert(swapped[i-1] == ns[min_i]);
            if k < i - 1 {
                if k == min_i {
                    assert(swapped[k] == ns[i-1]);
                    assert(ns[i-1] <= ns[min_i]);
                } else {
                    assert(swapped[k] == ns[k]);
                    assert(ns[k] <= ns[min_i]);
                }
            } else {
                assert(k == i - 1);
                assert(swapped[k] == ns[min_i]);
                assert(ns[min_i] <= ns[min_i]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(ns: &mut Vec<i32>) 
    requires old(ns).len() >= 0
    ensures 
        is_sorted(ns@),
        is_permutation2(old(ns)@, ns@),
// </vc-spec>
// <vc-code>
{
    let ghost orig_ns = ns@;
    let mut i: usize = 0;
    
    while i < ns.len()
        invariant
            i <= ns.len(),
            is_permutation2(orig_ns, ns@),
            forall|k: int, l: int| 0 <= k < l < i ==> #[trigger] ns[k] <= #[trigger] ns[l],
            forall|k: int, l: int| 0 <= k < i && i <= l < ns.len() ==> #[trigger] ns[k] <= #[trigger] ns[l],
        decreases ns.len() - i,
    {
        let min_i = find_min_index(ns, i, ns.len());
        
        assert(min_i >= i && min_i < ns.len());
        assert(forall|k: int| i <= k < ns.len() ==> ns[min_i as int] <= ns[k]);
        
        if i != min_i {
            let ghost old_ns = ns@;
            let temp = ns[i];
            let min_val = ns[min_i];
            ns.set(i, min_val);
            ns.set(min_i, temp);
            
            proof {
                lemma_swap_maintains_permutation(old_ns, i as int, min_i as int);
                lemma_permutation_transitive(orig_ns, old_ns, ns@);
                
                assert forall|k: int, l: int| 0 <= k < l < i + 1 implies #[trigger] ns[k] <= #[trigger] ns[l] by {
                    if l < i {
                        assert(ns[k] == old_ns[k]);
                        assert(ns[l] == old_ns[l]);
                    } else {
                        assert(l == i);
                        assert(ns[l] == old_ns[min_i as int]);
                        if k < i {
                            assert(ns[k] == old_ns[k]);
                            assert(old_ns[k] <= old_ns[min_i as int]);
                        }
                    }
                }
                
                assert forall|k: int, l: int| 0 <= k < i + 1 && i + 1 <= l < ns.len() implies #[trigger] ns[k] <= #[trigger] ns[l] by {
                    if k < i {
                        assert(ns[k] == old_ns[k]);
                        assert(old_ns[k] <= old_ns[l]);
                        assert(ns[l] == old_ns[l] || ns[l] == old_ns[i as int]);
                        assert(old_ns[i as int] >= old_ns[min_i as int]);
                    } else {
                        assert(k == i);
                        assert(ns[k] == old_ns[min_i as int]);
                        assert(old_ns[min_i as int] <= old_ns[l]);
                    }
                }
            }
        }
        
        i = i + 1;
    }
    
    assert(is_sorted(ns@)) by {
        assert forall|k: int, l: int| 0 <= k <= l < ns.len() implies #[trigger] ns[k] <= #[trigger] ns[l] by {
            if k < l {
                assert(ns[k] <= ns[l]);
            } else {
                assert(k == l);
                assert(ns[k] <= ns[k]);
            }
        }
    }
}
// </vc-code>

fn main() {}

}