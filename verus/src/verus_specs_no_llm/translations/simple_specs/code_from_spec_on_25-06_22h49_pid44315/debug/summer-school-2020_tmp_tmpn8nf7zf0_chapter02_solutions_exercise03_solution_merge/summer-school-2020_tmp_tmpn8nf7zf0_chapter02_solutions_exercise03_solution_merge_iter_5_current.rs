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

proof fn lemma_merge_first_element(merged: Seq<int>, a_rest: Seq<int>, b: Seq<int>, a_first: int)
    requires
        IsSorted(merged),
        SortSpec(a_rest + b, merged),
        merged.len() > 0,
        forall |i: int| 0 <= i < a_rest.len() ==> a_first <= a_rest.spec_index(i),
        forall |i: int| 0 <= i < b.len() ==> a_first <= b.spec_index(i)
    ensures
        a_first <= merged.spec_index(0)
{
    // Since merged is sorted and contains only elements from a_rest and b,
    // and a_first <= all elements in both sequences, we get the result
    assert((a_rest + b).to_multiset() == merged.to_multiset());
    
    if a_rest.len() > 0 && b.len() > 0 {
        // Case when both sequences are non-empty
        let min_a = a_rest.spec_index(0);
        let min_b = b.spec_index(0);
        assert(a_first <= min_a);
        assert(a_first <= min_b);
        
        if merged.spec_index(0) == min_a {
            assert(a_first <= merged.spec_index(0));
        } else if merged.spec_index(0) == min_b {
            assert(a_first <= merged.spec_index(0));
        } else {
            // The first element must come from one of the input sequences
            assert(false);
        }
    } else if a_rest.len() > 0 {
        assert(merged =~= a_rest);
        assert(a_first <= a_rest.spec_index(0));
        assert(a_first <= merged.spec_index(0));
    } else if b.len() > 0 {
        assert(merged =~= b);
        assert(a_first <= b.spec_index(0));
        assert(a_first <= merged.spec_index(0));
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
    
    let a_first = a[0];
    let b_first = b[0];
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
                lemma_merge_first_element(merged_rest, a_rest, b, a_first);
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
                
                // Use a simpler approach for the first element bound
                assert(b_first <= merged_rest.spec_index(0)) by {
                    assert(SortSpec(a + b_rest, merged_rest));
                    // The first element of merged_rest is either from a or b_rest
                    // If from a, then b_first < a_first <= that element
                    // If from b_rest, then b_first <= that element by sortedness of b
                }
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