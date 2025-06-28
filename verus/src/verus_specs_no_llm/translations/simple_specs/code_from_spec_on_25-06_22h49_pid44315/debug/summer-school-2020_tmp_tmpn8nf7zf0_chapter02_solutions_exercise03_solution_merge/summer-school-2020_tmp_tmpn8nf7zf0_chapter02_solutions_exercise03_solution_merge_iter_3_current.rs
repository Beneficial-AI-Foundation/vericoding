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
            // By induction on sortedness
            let mut j = 0;
            while j < i
                invariant 0 <= j <= i < s.len(), s.spec_index(0) <= s.spec_index(j)
            {
                assert(s.spec_index(j) <= s.spec_index(j+1));
                j = j + 1;
            }
        }
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
            // Prove sortedness
            assert forall |i: int| 0 <= i < result.len()-1 implies result.spec_index(i) <= result.spec_index(i+1) by {
                if i == 0 {
                    if merged_rest.len() > 0 {
                        assert(result.spec_index(0) == a_first);
                        assert(result.spec_index(1) == merged_rest.spec_index(0));
                        // merged_rest is merge of a_rest and b, so its first element
                        // is either from a_rest (>= a_first by sortedness) or from b (>= b_first >= a_first)
                        assert(IsSorted(merged_rest));
                        assert(SortSpec(a_rest + b, merged_rest));
                        assert(merged_rest.to_multiset() == (a_rest + b).to_multiset());
                        // Since merged_rest contains elements from a_rest and b,
                        // and a_first <= all elements in a_rest and a_first <= b_first <= all elements in b
                        assert(a_first <= merged_rest.spec_index(0));
                    }
                } else {
                    // For i > 0, we're comparing elements within merged_rest
                    assert(result.spec_index(i) == merged_rest.spec_index(i-1));
                    assert(result.spec_index(i+1) == merged_rest.spec_index(i));
                    assert(IsSorted(merged_rest));
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
            // Prove sortedness
            assert forall |i: int| 0 <= i < result.len()-1 implies result.spec_index(i) <= result.spec_index(i+1) by {
                if i == 0 {
                    if merged_rest.len() > 0 {
                        assert(result.spec_index(0) == b_first);
                        assert(result.spec_index(1) == merged_rest.spec_index(0));
                        // merged_rest is merge of a and b_rest, so its first element
                        // is either from a (> b_first) or from b_rest (>= b_first by sortedness)
                        assert(IsSorted(merged_rest));
                        assert(SortSpec(a + b_rest, merged_rest));
                        assert(b_first < a_first);
                        assert(b_first <= merged_rest.spec_index(0));
                    }
                } else {
                    // For i > 0, we're comparing elements within merged_rest
                    assert(result.spec_index(i) == merged_rest.spec_index(i-1));
                    assert(result.spec_index(i+1) == merged_rest.spec_index(i));
                    assert(IsSorted(merged_rest));
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