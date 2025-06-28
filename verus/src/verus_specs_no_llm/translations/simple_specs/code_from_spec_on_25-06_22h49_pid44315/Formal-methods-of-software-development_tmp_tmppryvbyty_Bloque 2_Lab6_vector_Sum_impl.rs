use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        v[0] + sum(v.subrange(1, v.len() as int))
    }
}

// Simplified lemma to show that sum of a prefix can be extended by one element
proof fn lemma_sum_extend_one(v: Seq<int>, i: nat)
    requires
        i < v.len()
    ensures
        sum(v.subrange(0, (i + 1) as int)) == sum(v.subrange(0, i as int)) + v[i as int]
    decreases i
{
    if i == 0 {
        // Base case: sum(v[0..1]) == sum(v[0..0]) + v[0]
        let empty_prefix = v.subrange(0, 0);
        let one_elem_prefix = v.subrange(0, 1);
        
        assert(empty_prefix.len() == 0);
        assert(sum(empty_prefix) == 0);
        
        assert(one_elem_prefix.len() == 1);
        assert(one_elem_prefix[0] == v[0]);
        
        // By definition of sum for non-empty sequence
        assert(sum(one_elem_prefix) == one_elem_prefix[0] + sum(one_elem_prefix.subrange(1, 1)));
        assert(one_elem_prefix.subrange(1, 1).len() == 0);
        assert(sum(one_elem_prefix.subrange(1, 1)) == 0);
        assert(sum(one_elem_prefix) == one_elem_prefix[0]);
        assert(sum(one_elem_prefix) == v[0]);
    } else {
        // Inductive case: assume the lemma holds for i-1
        lemma_sum_extend_one(v, (i - 1) as nat);
        
        let prefix_i = v.subrange(0, i as int);
        let prefix_i_plus_1 = v.subrange(0, (i + 1) as int);
        
        // Both prefixes are non-empty since i >= 1
        assert(prefix_i.len() > 0);
        assert(prefix_i_plus_1.len() > 0);
        assert(prefix_i[0] == v[0]);
        assert(prefix_i_plus_1[0] == v[0]);
        
        // By definition of sum
        assert(sum(prefix_i) == v[0] + sum(prefix_i.subrange(1, prefix_i.len() as int)));
        assert(sum(prefix_i_plus_1) == v[0] + sum(prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int)));
        
        // The tails are subranges of the original sequence
        assert(prefix_i.subrange(1, prefix_i.len() as int) =~= v.subrange(1, i as int));
        assert(prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int) =~= v.subrange(1, (i + 1) as int));
        
        // So we have:
        assert(sum(prefix_i) == v[0] + sum(v.subrange(1, i as int)));
        assert(sum(prefix_i_plus_1) == v[0] + sum(v.subrange(1, (i + 1) as int)));
        
        // From the inductive hypothesis applied to the original sequence v with index i-1:
        // sum(v.subrange(0, i)) == sum(v.subrange(0, i-1)) + v[i-1]
        // We know this is true, and now we need to show the relationship between
        // v.subrange(1, i+1) and v.subrange(1, i) + v[i]
        
        // Key insight: v.subrange(1, i+1) extends v.subrange(1, i) by one element v[i]
        let tail_i = v.subrange(1, i as int);
        let tail_i_plus_1 = v.subrange(1, (i + 1) as int);
        
        if i == 1 {
            // Special case: tail_i is empty, tail_i_plus_1 has one element
            assert(tail_i.len() == 0);
            assert(tail_i_plus_1.len() == 1);
            assert(sum(tail_i) == 0);
            assert(tail_i_plus_1[0] == v[1]);
            assert(sum(tail_i_plus_1) == tail_i_plus_1[0] + sum(tail_i_plus_1.subrange(1, 1)));
            assert(tail_i_plus_1.subrange(1, 1).len() == 0);
            assert(sum(tail_i_plus_1) == tail_i_plus_1[0]);
            assert(sum(tail_i_plus_1) == v[1]);
            assert(v[i as int] == v[1]);
            assert(sum(tail_i_plus_1) == sum(tail_i) + v[i as int]);
        } else {
            // General case: use the sum definition
            assert(tail_i_plus_1.len() > 0);
            assert(tail_i_plus_1[0] == v[1]);
            assert(sum(tail_i_plus_1) == tail_i_plus_1[0] + sum(tail_i_plus_1.subrange(1, tail_i_plus_1.len() as int)));
            
            // The tail of tail_i_plus_1 is v.subrange(2, i+1)
            // The sum of tail_i is either 0 (if i == 1) or v[1] + sum(v.subrange(2, i))
            if tail_i.len() == 0 {
                assert(sum(tail_i) == 0);
            } else {
                assert(sum(tail_i) == tail_i[0] + sum(tail_i.subrange(1, tail_i.len() as int)));
                assert(tail_i[0] == v[1]);
                assert(tail_i.subrange(1, tail_i.len() as int) =~= v.subrange(2, i as int));
            }
            
            // We can show that tail_i_plus_1 extends tail_i by the element v[i]
            assert(tail_i_plus_1.subrange(1, tail_i_plus_1.len() as int) =~= v.subrange(2, (i + 1) as int));
            
            // The relationship: v.subrange(2, i+1) extends v.subrange(2, i) by v[i]
            // This follows from the structure of subranges
            assert(sum(tail_i_plus_1) == sum(tail_i) + v[i as int]);
        }
        
        // Now we can conclude:
        assert(sum(prefix_i_plus_1) == v[0] + sum(tail_i_plus_1));
        assert(sum(prefix_i_plus_1) == v[0] + sum(tail_i) + v[i as int]);
        assert(sum(prefix_i_plus_1) == sum(prefix_i) + v[i as int]);
    }
}

fn vector_Sum(v: Seq<int>) -> (x: int)
    ensures
        x == sum(v)
{
    let mut result = 0;
    let mut i: usize = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result == sum(v.subrange(0, i as int))
        decreases
            v.len() - i
    {
        proof {
            lemma_sum_extend_one(v, i);
        }
        result = result + v[i];
        i = i + 1;
    }
    
    proof {
        assert(i == v.len());
        assert(v.subrange(0, v.len() as int) =~= v);
    }
    
    result
}

fn main() {
}

}