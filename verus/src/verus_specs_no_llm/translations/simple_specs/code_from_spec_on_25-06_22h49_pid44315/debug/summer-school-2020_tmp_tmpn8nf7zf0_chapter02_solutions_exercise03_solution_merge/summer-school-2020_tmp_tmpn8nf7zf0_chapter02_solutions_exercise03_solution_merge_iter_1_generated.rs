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
        assert(a + b =~= b);
        return b;
    }
    if b.len() == 0 {
        assert(a + b =~= a);
        return a;
    }
    
    let a_first = a.spec_index(0);
    let b_first = b.spec_index(0);
    let a_rest = a.subrange(1, a.len() as int);
    let b_rest = b.subrange(1, b.len() as int);
    
    if a_first <= b_first {
        let merged_rest = merge(a_rest, b);
        let result = seq![a_first] + merged_rest;
        
        // Prove sortedness
        assert forall |i: int| 0 <= i < result.len()-1 implies result.spec_index(i) <= result.spec_index(i+1) by {
            if i == 0 {
                if merged_rest.len() > 0 {
                    assert(result.spec_index(0) == a_first);
                    assert(result.spec_index(1) == merged_rest.spec_index(0));
                    // merged_rest.spec_index(0) is either from a_rest or b
                    // In both cases, it's >= a_first
                }
            } else {
                assert(result.spec_index(i) == merged_rest.spec_index(i-1));
                assert(result.spec_index(i+1) == merged_rest.spec_index(i));
            }
        };
        
        // Prove multiset equality
        assert((a + b).to_multiset() =~= (seq![a_first] + a_rest + b).to_multiset());
        assert((seq![a_first] + a_rest + b).to_multiset() =~= (seq![a_first] + (a_rest + b)).to_multiset());
        assert(result.to_multiset() =~= (seq![a_first] + merged_rest).to_multiset());
        
        return result;
    } else {
        let merged_rest = merge(a, b_rest);
        let result = seq![b_first] + merged_rest;
        
        // Prove sortedness
        assert forall |i: int| 0 <= i < result.len()-1 implies result.spec_index(i) <= result.spec_index(i+1) by {
            if i == 0 {
                if merged_rest.len() > 0 {
                    assert(result.spec_index(0) == b_first);
                    assert(result.spec_index(1) == merged_rest.spec_index(0));
                    // merged_rest.spec_index(0) is either from a or b_rest
                    // In both cases, it's >= b_first
                }
            } else {
                assert(result.spec_index(i) == merged_rest.spec_index(i-1));
                assert(result.spec_index(i+1) == merged_rest.spec_index(i));
            }
        };
        
        // Prove multiset equality
        assert((a + b).to_multiset() =~= (a + seq![b_first] + b_rest).to_multiset());
        assert((a + seq![b_first] + b_rest).to_multiset() =~= (seq![b_first] + (a + b_rest)).to_multiset());
        assert(result.to_multiset() =~= (seq![b_first] + merged_rest).to_multiset());
        
        return result;
    }
}

}