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
        
        // Key insight: prefix_i_plus_1 can be split as first element + tail
        assert(prefix_i_plus_1.len() > 0);
        assert(prefix_i_plus_1[0] == v[0]);
        
        let tail_i_plus_1 = prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int);
        assert(tail_i_plus_1 =~= v.subrange(1, (i + 1) as int));
        
        // By definition of sum
        assert(sum(prefix_i_plus_1) == prefix_i_plus_1[0] + sum(tail_i_plus_1));
        assert(sum(prefix_i_plus_1) == v[0] + sum(v.subrange(1, (i + 1) as int)));
        
        // Similarly for prefix_i
        if i > 0 {
            assert(prefix_i.len() > 0);
            assert(prefix_i[0] == v[0]);
            let tail_i = prefix_i.subrange(1, prefix_i.len() as int);
            assert(tail_i =~= v.subrange(1, i as int));
            assert(sum(prefix_i) == v[0] + sum(v.subrange(1, i as int)));
        } else {
            assert(prefix_i.len() == 0);
            assert(sum(prefix_i) == 0);
        }
        
        // Now we need to show: sum(v.subrange(1, i+1)) == sum(v.subrange(1, i)) + v[i]
        // This follows from applying the lemma to the tail of v
        let v_tail = v.subrange(1, v.len() as int);
        assert(v_tail.len() == v.len() - 1);
        assert((i - 1) as nat < v_tail.len());
        
        lemma_sum_extend_one(v_tail, (i - 1) as nat);
        
        // The lemma on v_tail gives us:
        // sum(v_tail.subrange(0, i)) == sum(v_tail.subrange(0, i-1)) + v_tail[i-1]
        assert(v_tail.subrange(0, i as int) =~= v.subrange(1, (i + 1) as int));
        assert(v_tail.subrange(0, (i - 1) as int) =~= v.subrange(1, i as int));
        assert(v_tail[(i - 1) as int] == v[i as int]);
        
        // Therefore: sum(v.subrange(1, i+1)) == sum(v.subrange(1, i)) + v[i]
        assert(sum(v.subrange(1, (i + 1) as int)) == sum(v.subrange(1, i as int)) + v[i as int]);
        
        // Combining everything:
        assert(sum(prefix_i_plus_1) == v[0] + sum(v.subrange(1, (i + 1) as int)));
        assert(sum(prefix_i_plus_1) == v[0] + sum(v.subrange(1, i as int)) + v[i as int]);
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