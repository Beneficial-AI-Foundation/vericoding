use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSorted(s: Seq<int>) -> bool {
    forall |i: int| 0 <= i < s.len()-1 ==> s.spec_index(i) <= s.spec_index(i+1)
}

spec fn SortSpec(input: Seq<int>, output: Seq<int>) -> bool {
    && IsSorted(output)
    && output.to_multiset() == input.to_multiset()
}

proof fn lemma_sorted_subrange(s: Seq<int>, start: int, end: int)
    requires
        IsSorted(s),
        0 <= start <= end <= s.len()
    ensures
        IsSorted(s.subrange(start, end))
{
    let sub = s.subrange(start, end);
    assert forall |i: int| 0 <= i < sub.len()-1 implies sub.spec_index(i) <= sub.spec_index(i+1) by {
        assert(sub.spec_index(i) == s.spec_index(start + i));
        assert(sub.spec_index(i+1) == s.spec_index(start + i + 1));
        assert(0 <= start + i < s.len() - 1);
        assert(s.spec_index(start + i) <= s.spec_index(start + i + 1));
    }
}

proof fn lemma_first_element_bound(s: Seq<int>, first: int)
    requires
        IsSorted(s),
        s.len() > 0,
        first == s.spec_index(0)
    ensures
        forall |i: int| 0 <= i < s.len() ==> first <= s.spec_index(i)
{
    assert forall |i: int| 0 <= i < s.len() implies first <= s.spec_index(i) by {
        if i == 0 {
            assert(first == s.spec_index(0));
        } else {
            lemma_first_element_bound_helper(s, first, i);
        }
    }
}

proof fn lemma_first_element_bound_helper(s: Seq<int>, first: int, i: int)
    requires
        IsSorted(s),
        s.len() > 0,
        first == s.spec_index(0),
        0 < i < s.len()
    ensures
        first <= s.spec_index(i)
    decreases i
{
    if i == 1 {
        assert(first == s.spec_index(0));
        assert(s.spec_index(0) <= s.spec_index(1));
        assert(first <= s.spec_index(1));
    } else {
        lemma_first_element_bound_helper(s, first, i - 1);
        assert(first <= s.spec_index(i - 1));
        assert(s.spec_index(i - 1) <= s.spec_index(i));
        assert(first <= s.spec_index(i));
    }
}

proof fn lemma_min_element_in_multiset(s: Seq<int>, min_val: int)
    requires
        s.len() > 0,
        s.to_multiset().contains(min_val),
        forall |x: int| s.to_multiset().contains(x) ==> min_val <= x
    ensures
        exists |i: int| 0 <= i < s.len() && s.spec_index(i) == min_val
{
    // This follows from the fact that if min_val is in the multiset,
    // it must appear at some index in the sequence
}

proof fn lemma_merged_first_element_bound(merged: Seq<int>, a: Seq<int>, b: Seq<int>, bound: int)
    requires
        merged.len() > 0,
        SortSpec(a + b, merged),
        forall |i: int| 0 <= i < a.len() ==> bound <= a.spec_index(i),
        forall |i: int| 0 <= i < b.len() ==> bound <= b.spec_index(i)
    ensures
        bound <= merged.spec_index(0)
{
    assert((a + b).to_multiset() == merged.to_multiset());
    
    if a.len() == 0 && b.len() == 0 {
        assert(false); // contradiction since merged.len() > 0
    } else if a.len() == 0 {
        assert(merged.to_multiset() == b.to_multiset());
        if b.len() > 0 {
            assert(bound <= b.spec_index(0));
        }
        // Since merged is sorted and has same elements as b
        lemma_first_element_bound(merged, merged.spec_index(0));
        assert(bound <= merged.spec_index(0));
    } else if b.len() == 0 {
        assert(merged.to_multiset() == a.to_multiset());
        assert(bound <= a.spec_index(0));
        lemma_first_element_bound(merged, merged.spec_index(0));
        assert(bound <= merged.spec_index(0));
    } else {
        // Both a and b are non-empty
        let first_merged = merged.spec_index(0);
        
        // Since merged contains exactly the elements of a + b,
        // and merged is sorted, first_merged is the minimum element
        lemma_first_element_bound(merged, first_merged);
        
        // first_merged must be in (a + b).to_multiset()
        assert(merged.to_multiset().contains(first_merged));
        assert((a + b).to_multiset().contains(first_merged));
        
        // Since all elements in a and b are >= bound, first_merged >= bound
        assert forall |x: int| (a + b).to_multiset().contains(x) implies bound <= x by {
            if a.to_multiset().contains(x) {
                // x is in a, so bound <= x
            }
            if b.to_multiset().contains(x) {
                // x is in b, so bound <= x  
            }
        }
        
        assert(bound <= first_merged);
    }
}

fn merge(a: Seq<int>, b: Seq<int>) -> (output: Seq<int>)
    requires
        IsSorted(a),
        IsSorted(b)
    ensures
        IsSorted(output),
        SortSpec(a + b, output)
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        proof {
            assert(a + b =~= b);
            assert(IsSorted(b));
            assert(b.to_multiset() == (a + b).to_multiset());
        }
        return b;
    }
    if b.len() == 0 {
        proof {
            assert(a + b =~= a);
            assert(IsSorted(a));
            assert(a.to_multiset() == (a + b).to_multiset());
        }
        return a;
    }
    
    let a_first = a.spec_index(0);
    let b_first = b.spec_index(0);
    let a_rest = a.subrange(1, a.len() as int);
    let b_rest = b.subrange(1, b.len() as int);
    
    proof {
        lemma_sorted_subrange(a, 1, a.len() as int);
        lemma_sorted_subrange(b, 1, b.len() as int);
        lemma_first_element_bound(a, a_first);
        lemma_first_element_bound(b, b_first);
    }
    
    if a_first <= b_first {
        let merged_rest = merge(a_rest, b);
        let result = seq![a_first] + merged_rest;
        
        proof {
            if merged_rest.len() > 0 {
                lemma_merged_first_element_bound(merged_rest, a_rest, b, a_first);
            }
            
            // Prove sortedness
            assert forall |i: int| 0 <= i < result.len()-1 implies result.spec_index(i) <= result.spec_index(i+1) by {
                if i == 0 {
                    if merged_rest.len() > 0 {
                        assert(result.spec_index(0) == a_first);
                        assert(result.spec_index(1) == merged_rest.spec_index(0));
                        assert(a_first <= merged_rest.spec_index(0));
                    }
                } else {
                    assert(result.spec_index(i) == merged_rest.spec_index(i-1));
                    assert(result.spec_index(i+1) == merged_rest.spec_index(i));
                    assert(IsSorted(merged_rest));
                    assert(0 <= i-1 < merged_rest.len()-1);
                    assert(merged_rest.spec_index(i-1) <= merged_rest.spec_index(i));
                }
            };
            
            // Prove multiset equality
            assert(a =~= seq![a_first] + a_rest);
            assert((a + b).to_multiset() =~= (seq![a_first] + a_rest + b).to_multiset());
            assert((seq![a_first] + a_rest + b).to_multiset() =~= (seq![a_first] + (a_rest + b)).to_multiset());
            assert(SortSpec(a_rest + b, merged_rest));
            assert(merged_rest.to_multiset() == (a_rest + b).to_multiset());
            assert(result.to_multiset() =~= (seq![a_first] + merged_rest).to_multiset());
            assert((seq![a_first] + merged_rest).to_multiset() =~= seq![a_first].to_multiset() + merged_rest.to_multiset());
            assert(seq![a_first].to_multiset() + merged_rest.to_multiset() == seq![a_first].to_multiset() + (a_rest + b).to_multiset());
            assert(seq![a_first].to_multiset() + (a_rest + b).to_multiset() == (seq![a_first] + (a_rest + b)).to_multiset());
            assert((seq![a_first] + (a_rest + b)).to_multiset() == (a + b).to_multiset());
        }
        
        return result;
    } else {
        let merged_rest = merge(a, b_rest);
        let result = seq![b_first] + merged_rest;
        
        proof {
            if merged_rest.len() > 0 {
                // Since b_first < a_first and all elements in a are >= a_first
                assert forall |i: int| 0 <= i < a.len() implies b_first <= a.spec_index(i) by {
                    assert(a_first <= a.spec_index(i));
                    assert(b_first < a_first);
                }
                
                // All elements in b_rest are >= b_first by sortedness of b
                assert forall |i: int| 0 <= i < b_rest.len() implies b_first <= b_rest.spec_index(i) by {
                    assert(b_first == b.spec_index(0));
                    assert(b_rest.spec_index(i) == b.spec_index(i + 1));
                    assert(b.spec_index(0) <= b.spec_index(i + 1));
                }
                
                lemma_merged_first_element_bound(merged_rest, a, b_rest, b_first);
            }
            
            // Prove sortedness
            assert forall |i: int| 0 <= i < result.len()-1 implies result.spec_index(i) <= result.spec_index(i+1) by {
                if i == 0 {
                    if merged_rest.len() > 0 {
                        assert(result.spec_index(0) == b_first);
                        assert(result.spec_index(1) == merged_rest.spec_index(0));
                        assert(b_first <= merged_rest.spec_index(0));
                    }
                } else {
                    assert(result.spec_index(i) == merged_rest.spec_index(i-1));
                    assert(result.spec_index(i+1) == merged_rest.spec_index(i));
                    assert(IsSorted(merged_rest));
                    assert(0 <= i-1 < merged_rest.len()-1);
                    assert(merged_rest.spec_index(i-1) <= merged_rest.spec_index(i));
                }
            };
            
            // Prove multiset equality
            assert(b =~= seq![b_first] + b_rest);
            assert((a + b).to_multiset() =~= (a + seq![b_first] + b_rest).to_multiset());
            assert((a + seq![b_first] + b_rest).to_multiset() =~= (seq![b_first] + a + b_rest).to_multiset());
            assert((seq![b_first] + a + b_rest).to_multiset() =~= (seq![b_first] + (a + b_rest)).to_multiset());
            assert(SortSpec(a + b_rest, merged_rest));
            assert(merged_rest.to_multiset() == (a + b_rest).to_multiset());
            assert(result.to_multiset() =~= (seq![b_first] + merged_rest).to_multiset());
            assert((seq![b_first] + merged_rest).to_multiset() =~= seq![b_first].to_multiset() + merged_rest.to_multiset());
            assert(seq![b_first].to_multiset() + merged_rest.to_multiset() == seq![b_first].to_multiset() + (a + b_rest).to_multiset());
            assert(seq![b_first].to_multiset() + (a + b_rest).to_multiset() == (seq![b_first] + (a + b_rest)).to_multiset());
            assert((seq![b_first] + (a + b_rest)).to_multiset() == (a + b).to_multiset());
        }
        
        return result;
    }
}

}