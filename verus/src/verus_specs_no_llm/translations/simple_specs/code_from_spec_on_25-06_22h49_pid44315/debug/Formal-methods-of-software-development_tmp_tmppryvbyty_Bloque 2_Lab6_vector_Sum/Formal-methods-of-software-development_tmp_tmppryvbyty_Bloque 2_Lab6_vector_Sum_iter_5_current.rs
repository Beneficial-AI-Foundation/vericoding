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
        // Base case: extending from empty sequence to single element
        assert(v.subrange(0, 1).len() == 1);
        assert(v.subrange(0, 1)[0] == v[0]);
        assert(v.subrange(0, 0).len() == 0);
        assert(sum(v.subrange(0, 0)) == 0);
        assert(sum(v.subrange(0, 1)) == v[0] + sum(v.subrange(1, 1)));
        assert(v.subrange(1, 1).len() == 0);
        assert(sum(v.subrange(1, 1)) == 0);
        assert(sum(v.subrange(0, 1)) == v[0]);
        assert(sum(v.subrange(0, 0)) + v[0] == 0 + v[0]);
    } else {
        // Inductive case
        lemma_sum_extend(v, i - 1);
        
        // We know: sum(v.subrange(0, i)) == sum(v.subrange(0, i-1)) + v[i-1]
        // We want: sum(v.subrange(0, i+1)) == sum(v.subrange(0, i)) + v[i]
        
        // Use the definition of sum
        assert(sum(v.subrange(0, i + 1)) == v[0] + sum(v.subrange(0, i + 1).subrange(1, (i + 1) as int)));
        assert(sum(v.subrange(0, i)) == v[0] + sum(v.subrange(0, i).subrange(1, i as int)));
        
        // Show that the tail sequences are related
        assert(v.subrange(0, i + 1).subrange(1, (i + 1) as int) =~= v.subrange(1, i + 1));
        assert(v.subrange(0, i).subrange(1, i as int) =~= v.subrange(1, i));
        
        // Apply the lemma recursively to the tail
        if i > 1 {
            lemma_sum_extend(v.subrange(1, v.len() as int), i - 1);
        }
        
        // The key insight: sum(v.subrange(1, i+1)) == sum(v.subrange(1, i)) + v[i]
        assert(sum(v.subrange(1, i + 1)) == sum(v.subrange(1, i)) + v[i]);
        
        // Combine everything
        assert(sum(v.subrange(0, i + 1)) == v[0] + sum(v.subrange(1, i + 1)));
        assert(sum(v.subrange(0, i + 1)) == v[0] + sum(v.subrange(1, i)) + v[i]);
        assert(sum(v.subrange(0, i + 1)) == sum(v.subrange(0, i)) + v[i]);
    }
}

// Simpler helper lemma that's easier to prove
proof fn lemma_sum_split(v: Seq<int>, i: int)
    requires
        0 <= i <= v.len()
    ensures
        sum(v.subrange(0, i)) + (if i < v.len() { v[i] } else { 0 }) == 
        sum(v.subrange(0, if i < v.len() { i + 1 } else { i }))
{
    if i == v.len() {
        // Nothing to add
    } else if i == 0 {
        assert(v.subrange(0, 0).len() == 0);
        assert(sum(v.subrange(0, 0)) == 0);
        assert(v.subrange(0, 1).len() == 1);
        assert(sum(v.subrange(0, 1)) == v[0] + sum(v.subrange(1, 1)));
        assert(v.subrange(1, 1).len() == 0);
        assert(sum(v.subrange(1, 1)) == 0);
    } else {
        lemma_sum_split(v, i - 1);
        lemma_sum_extend(v, i);
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
            lemma_sum_split(v, i as int);
        }
        result = result + v[i];
        i = i + 1;
    }
    
    assert(i == v.len());
    assert(v.subrange(0, v.len() as int) =~= v);
    result
}

fn main() {
}

}