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
        assert(sum(v1) == v1[0]);
        assert(v1[0] == v[0]);
    } else {
        // Inductive case
        lemma_sum_extend_one(v, (i - 1) as nat);
        
        // We know from IH: sum(v.subrange(0, i)) == sum(v.subrange(0, i-1)) + v[i-1]
        // We want to show: sum(v.subrange(0, i+1)) == sum(v.subrange(0, i)) + v[i]
        
        let vi = v.subrange(0, i as int);
        let vi1 = v.subrange(0, (i + 1) as int);
        
        // Show that vi1 = vi + [v[i]]
        assert(vi1.len() == vi.len() + 1);
        assert(forall|j: int| 0 <= j < vi.len() ==> vi1[j] == vi[j]);
        assert(vi1[i as int] == v[i as int]);
        
        // Apply sum definition to vi1
        assert(vi1.len() > 0);
        assert(sum(vi1) == vi1[0] + sum(vi1.subrange(1, vi1.len() as int)));
        
        // Apply sum definition to vi
        if vi.len() == 0 {
            assert(sum(vi) == 0);
            assert(vi1.len() == 1);
            assert(sum(vi1) == vi1[0]);
            assert(vi1[0] == v[0]);
            assert(v[0] == v[i as int]); // since i == 0 would be handled in base case, this is i > 0
        } else {
            assert(sum(vi) == vi[0] + sum(vi.subrange(1, vi.len() as int)));
            
            // Key insight: vi1.subrange(1, vi1.len()) == vi.subrange(1, vi.len()) + [v[i]]
            let tail_vi = vi.subrange(1, vi.len() as int);
            let tail_vi1 = vi1.subrange(1, vi1.len() as int);
            
            // tail_vi1 is v.subrange(1, i+1) and tail_vi is v.subrange(1, i)
            assert(tail_vi1 =~= v.subrange(1, (i + 1) as int));
            assert(tail_vi =~= v.subrange(1, i as int));
            
            // Apply the lemma recursively to the tail
            if i > 1 {
                let v_tail = v.subrange(1, v.len() as int);
                assert(v_tail.len() == v.len() - 1);
                assert((i - 1) as nat < v_tail.len());
                lemma_sum_extend_one(v_tail, (i - 1) as nat);
                assert(sum(v_tail.subrange(0, i as int)) == sum(v_tail.subrange(0, (i - 1) as int)) + v_tail[(i - 1) as int]);
                assert(v_tail.subrange(0, i as int) =~= v.subrange(1, (i + 1) as int));
                assert(v_tail.subrange(0, (i - 1) as int) =~= v.subrange(1, i as int));
                assert(v_tail[(i - 1) as int] == v[i as int]);
            } else {
                // i == 1, so tail_vi.len() == 0 and tail_vi1.len() == 1
                assert(tail_vi.len() == 0);
                assert(sum(tail_vi) == 0);
                assert(tail_vi1.len() == 1);
                assert(tail_vi1[0] == v[i as int]);
                assert(sum(tail_vi1) == tail_vi1[0]);
            }
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