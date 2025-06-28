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
        sum(v.subrange(0, (i + 1) as int)) == sum(v.subrange(0, i as int)) + v[i as int]
{
    if i == 0 {
        assert(v.subrange(0, 1) =~= seq![v[0]]);
        assert(v.subrange(0, 0) =~= seq![]);
        assert(sum(v.subrange(0, 0)) == 0);
        assert(sum(v.subrange(0, 1)) == v[0] + sum(seq![]) == v[0] + 0 == v[0]);
    } else {
        let sub_i = v.subrange(0, i as int);
        let sub_i_plus_1 = v.subrange(0, (i + 1) as int);
        
        // Both subsequences start with the same element
        assert(sub_i_plus_1[0] == v[0]);
        assert(sub_i[0] == v[0]);
        
        // The tail of sub_i_plus_1 is v.subrange(1, i+1)
        assert(sub_i_plus_1.subrange(1, sub_i_plus_1.len() as int) =~= v.subrange(1, (i + 1) as int));
        // The tail of sub_i is v.subrange(1, i)
        assert(sub_i.subrange(1, sub_i.len() as int) =~= v.subrange(1, i as int));
        
        // Apply the lemma recursively to the tail
        lemma_sum_extend(v.subrange(1, v.len() as int), i - 1);
        
        // Now we can conclude the result
        assert(sum(sub_i_plus_1) == v[0] + sum(v.subrange(1, (i + 1) as int)));
        assert(sum(sub_i) == v[0] + sum(v.subrange(1, i as int)));
        assert(sum(v.subrange(1, (i + 1) as int)) == sum(v.subrange(1, i as int)) + v[i as int]);
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