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
        assert(v.subrange(0, 0).len() == 0);
        assert(sum(v.subrange(0, 0)) == 0);
        
        let v1 = v.subrange(0, 1);
        assert(v1.len() == 1);
        assert(v1[0] == v[0]);
        assert(sum(v1) == v1[0] + sum(v1.subrange(1, 1)));
        assert(v1.subrange(1, 1).len() == 0);
        assert(sum(v1.subrange(1, 1)) == 0);
        assert(sum(v1) == v1[0] == v[0]);
    } else {
        // Inductive case
        lemma_sum_extend_one(v, (i - 1) as nat);
        
        // We know: sum(v.subrange(0, i)) == sum(v.subrange(0, i-1)) + v[i-1]
        // We want: sum(v.subrange(0, i+1)) == sum(v.subrange(0, i)) + v[i]
        
        let vi = v.subrange(0, i as int);
        let vi1 = v.subrange(0, (i + 1) as int);
        
        // Apply definition of sum to vi1
        assert(vi1.len() > 0);
        assert(sum(vi1) == vi1[0] + sum(vi1.subrange(1, vi1.len() as int)));
        assert(vi1[0] == v[0]);
        
        // The tail of vi1 is v.subrange(1, i+1)
        let tail_vi1 = vi1.subrange(1, vi1.len() as int);
        assert(tail_vi1 =~= v.subrange(1, (i + 1) as int));
        
        // Similarly for vi
        if vi.len() > 0 {
            assert(sum(vi) == vi[0] + sum(vi.subrange(1, vi.len() as int)));
            assert(vi[0] == v[0]);
            let tail_vi = vi.subrange(1, vi.len() as int);
            assert(tail_vi =~= v.subrange(1, i as int));
            
            // Apply induction to the tail
            let v_tail = v.subrange(1, v.len() as int);
            lemma_sum_extend_one(v_tail, (i - 1) as nat);
            
            assert(sum(v.subrange(1, (i + 1) as int)) == sum(v.subrange(1, i as int)) + v[i as int]);
        }
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
        
        proof {
            assert(result == sum(v.subrange(0, (i - 1) as int)) + v[(i - 1) as int]);
            assert(result == sum(v.subrange(0, i as int)));
        }
    }
    
    proof {
        assert(i == v.len());
        assert(v.subrange(0, v.len() as int) =~= v);
        assert(result == sum(v));
    }
    
    result
}

fn main() {
}

}