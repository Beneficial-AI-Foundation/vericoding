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
                        // Since a is sorted and a_first is the first element
                        // and merged_rest contains elements from a_rest and b
                        // and a_first <= b_first, we know a_first <= merged_rest.spec_index(0)
                        if merged_rest.spec_index(0) == a_rest.spec_index(0) {
                            // From a_rest, so a_first <= a_rest.spec_index(0) by sortedness of a
                            assert(a.spec_index(0) <= a.spec_index(1));
                        } else {
                            // From b, so a_first <= b_first <= this element
                            assert(a_first <= b_first);
                        }
                    }
                } else {
                    // For i > 0, we're comparing elements within merged_rest
                    assert(result.spec_index(i) == merged_rest.spec_index(i-1));
                    assert(result.spec_index(i+1) == merged_rest.spec_index(i));
                    assert(IsSorted(merged_rest));
                    assert(merged_rest.spec_index(i-1) <= merged_rest.spec_index(i));
                }
            };
            
            // Prove multiset equality
            assert(a =~= seq![a_first] + a_rest);
            assert((a + b).to_multiset() =~= (seq![a_first] + a_rest + b).to_multiset());
            assert((seq![a_first] + a_rest + b).to_multiset() =~= (seq![a_first] + (a_rest + b)).to_multiset());
            assert(merged_rest.to_multiset() == (a_rest + b).to_multiset());
            assert(result.to_multiset() =~= (seq![a_first] + merged_rest).to_multiset());
            assert((seq![a_first] + merged_rest).to_multiset() =~= seq![a_first].to_multiset().add(merged_rest.to_multiset()));
            assert(seq![a_first].to_multiset().add(merged_rest.to_multiset()) == seq![a_first].to_multiset().add((a_rest + b).to_multiset()));
            assert(seq![a_first].to_multiset().add((a_rest + b).to_multiset()) == (seq![a_first] + (a_rest + b)).to_multiset());
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
                        // Since b is sorted and b_first is the first element
                        // and merged_rest contains elements from a and b_rest
                        // and b_first < a_first, we know b_first <= merged_rest.spec_index(0)
                        if merged_rest.spec_index(0) == b_rest.spec_index(0) {
                            // From b_rest, so b_first <= b_rest.spec_index(0) by sortedness of b
                            assert(b.spec_index(0) <= b.spec_index(1));
                        } else {
                            // From a, so b_first < a_first <= this element
                            assert(b_first < a_first);
                        }
                    }
                } else {
                    // For i > 0, we're comparing elements within merged_rest
                    assert(result.spec_index(i) == merged_rest.spec_index(i-1));
                    assert(result.spec_index(i+1) == merged_rest.spec_index(i));
                    assert(IsSorted(merged_rest));
                    assert(merged_rest.spec_index(i-1) <= merged_rest.spec_index(i));
                }
            };
            
            // Prove multiset equality
            assert(b =~= seq![b_first] + b_rest);
            assert((a + b).to_multiset() =~= (a + seq![b_first] + b_rest).to_multiset());
            assert((a + seq![b_first] + b_rest).to_multiset() =~= (seq![b_first] + (a + b_rest)).to_multiset());
            assert(merged_rest.to_multiset() == (a + b_rest).to_multiset());
            assert(result.to_multiset() =~= (seq![b_first] + merged_rest).to_multiset());
            assert((seq![b_first] + merged_rest).to_multiset() =~= seq![b_first].to_multiset().add(merged_rest.to_multiset()));
            assert(seq![b_first].to_multiset().add(merged_rest.to_multiset()) == seq![b_first].to_multiset().add((a + b_rest).to_multiset()));
            assert(seq![b_first].to_multiset().add((a + b_rest).to_multiset()) == (seq![b_first] + (a + b_rest)).to_multiset());
            assert((seq![b_first] + (a + b_rest)).to_multiset() == (a + b).to_multiset());
        }
        
        return result;
    }
}

}