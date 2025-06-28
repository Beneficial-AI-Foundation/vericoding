use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_prefix_sum_for(a: Vec<int>, c: Vec<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> 
        i + 1 < c.len() && 
        c.spec_index(i+1) == c.spec_index(i) + a.spec_index(i)
}

spec fn sum(a: Vec<int>, i: int, j: int) -> int 
    decreases j - i
{
    if i >= j {
        0
    } else {
        a.spec_index(i) + sum(a, i + 1, j)
    }
}

fn queryFast(a: Vec<int>, c: Vec<int>, i: usize, j: usize) -> (r: int)
    requires
        a.len() + 1 == c.len() && c.spec_index(0) == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a, c)
    ensures
        r == sum(a, i as int, j as int)
{
    proof {
        lemma_prefix_sum_property(a, c, i as int, j as int);
    }
    
    // Prove bounds for safe access
    assert(j < c.len()) by {
        assert(j <= a.len());
        assert(a.len() + 1 == c.len());
    };
    assert(i < c.len()) by {
        assert(i <= j);
        assert(j <= a.len());
        assert(a.len() + 1 == c.len());
    };
    
    // Access the elements
    let c_j = c[j];
    let c_i = c[i];
    
    // Connect concrete access to specification
    assert(c_j == c.spec_index(j as int));
    assert(c_i == c.spec_index(i as int));
    
    // Use the lemma result
    assert(c.spec_index(j as int) - c.spec_index(i as int) == sum(a, i as int, j as int));
    
    c_j - c_i
}

proof fn lemma_prefix_sum_property(a: Vec<int>, c: Vec<int>, i: int, j: int)
    requires
        a.len() + 1 == c.len() && c.spec_index(0) == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a, c)
    ensures
        c.spec_index(j) - c.spec_index(i) == sum(a, i, j)
    decreases j - i
{
    if i >= j {
        // Base case: empty range
        assert(sum(a, i, j) == 0);
        assert(c.spec_index(j) - c.spec_index(i) == 0);
    } else {
        // Inductive step
        lemma_prefix_sum_property(a, c, i + 1, j);
        
        // Establish bounds for the forall instantiation
        assert(0 <= i < a.len());
        assert(i + 1 < c.len()) by {
            assert(a.len() + 1 == c.len());
        };
        
        // From is_prefix_sum_for, we know that c[i+1] = c[i] + a[i]
        assert(c.spec_index(i+1) == c.spec_index(i) + a.spec_index(i)) by {
            assert(is_prefix_sum_for(a, c));
        };
        
        // From inductive hypothesis
        assert(c.spec_index(j) - c.spec_index(i+1) == sum(a, i + 1, j));
        
        // Rearrange the prefix sum relation
        assert(c.spec_index(i+1) - c.spec_index(i) == a.spec_index(i));
        
        // Algebraic manipulation - step by step
        assert((c.spec_index(j) - c.spec_index(i)) == 
               (c.spec_index(j) - c.spec_index(i+1)) + (c.spec_index(i+1) - c.spec_index(i))) by {
            // This is basic algebra: (a - b) = (a - c) + (c - b)
        };
        
        assert((c.spec_index(j) - c.spec_index(i+1)) + (c.spec_index(i+1) - c.spec_index(i)) == 
               sum(a, i + 1, j) + a.spec_index(i)) by {
            // From our established facts above
        };
        
        assert(sum(a, i + 1, j) + a.spec_index(i) == sum(a, i, j)) by {
            // This follows from the definition of sum
            assert(sum(a, i, j) == a.spec_index(i) + sum(a, i + 1, j));
        };
        
        // Therefore, by transitivity:
        assert(c.spec_index(j) - c.spec_index(i) == sum(a, i, j));
    }
}

}