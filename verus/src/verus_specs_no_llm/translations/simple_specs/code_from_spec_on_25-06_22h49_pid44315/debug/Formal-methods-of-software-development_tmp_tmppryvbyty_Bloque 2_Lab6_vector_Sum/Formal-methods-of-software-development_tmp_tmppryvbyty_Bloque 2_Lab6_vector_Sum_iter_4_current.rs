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

// Helper lemma to prove the relationship between subranges
proof fn lemma_sum_extend(v: Seq<int>, i: int)
    requires
        0 <= i < v.len()
    ensures
        sum(v.subrange(0, i + 1)) == sum(v.subrange(0, i)) + v[i]
    decreases i
{
    if i == 0 {
        assert(v.subrange(0, 1) =~= seq![v[0]]);
        assert(v.subrange(0, 0) =~= seq![]);
        assert(sum(v.subrange(0, 0)) == 0);
        assert(sum(v.subrange(0, 1)) == v[0] + sum(seq![]) == v[0] + 0 == v[0]);
    } else {
        // Use induction on a simpler subrange
        let v_tail = v.subrange(1, v.len() as int);
        lemma_sum_extend(v_tail, i - 1);
        
        // Now prove the relationship step by step
        assert(v.subrange(0, i + 1)[0] == v[0]);
        assert(v.subrange(0, i)[0] == v[0]);
        
        let tail_i_plus_1 = v.subrange(0, i + 1).subrange(1, (i + 1) as int);
        let tail_i = v.subrange(0, i).subrange(1, i as int);
        
        assert(tail_i_plus_1 =~= v.subrange(1, i + 1));
        assert(tail_i =~= v.subrange(1, i));
        
        // The key insight: the difference between the two sums is v[i]
        assert(sum(v.subrange(0, i + 1)) == v[0] + sum(v.subrange(1, i + 1)));
        assert(sum(v.subrange(0, i)) == v[0] + sum(v.subrange(1, i)));
        assert(sum(v.subrange(1, i + 1)) == sum(v.subrange(1, i)) + v[i]);
    }
}

fn vector_Sum(v: Seq<int>) -> (x: int)
    ensures
        x == sum(v)
{
    let mut result = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result == sum(v.subrange(0, i as int))
        decreases
            v.len() - i
    {
        proof {
            lemma_sum_extend(v, i as int);
        }
        result = result + v[i];
        i = i + 1;
    }
    
    assert(v.subrange(0, v.len() as int) =~= v);
    result
}

fn main() {
}

}