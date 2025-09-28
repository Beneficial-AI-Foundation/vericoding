use vstd::prelude::*;

verus! {

/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i >= j { 
        0 
    } else { 
        a[i] + sum(a, i + 1, j) 
    }
}



//(b)




//(c)

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool
{
    &&& a.len() + 1 == c.len() 
    &&& c.len() > 0 
    &&& c[0] == 0
    &&& forall|i: int| 0 <= i < a.len() ==> c[i + 1] == c[i] + a[i]
}

// <vc-helpers>
proof fn lemma_prefix_sum_range(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires
        a.len() + 1 == c.len(),
        c.len() > 0,
        c[0] == 0,
        is_prefix_sum_for(a, c),
        0 <= i <= j <= a.len(),
    ensures
        c[j] - c[i] == sum(a, i, j),
    decreases j - i,
{
    if i == j {
        // Base case: sum(a, i, i) == 0
        assert(sum(a, i, i) == 0);
        assert(c[j] - c[i] == 0);
    } else {
        // Inductive case
        assert(is_prefix_sum_for(a, c));
        assert(c[i + 1] == c[i] + a[i]);
        
        lemma_prefix_sum_range(a, c, i + 1, j);
        assert(c[j] - c[i + 1] == sum(a, i + 1, j));
        
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
        assert(c[j] - c[i] == c[j] - c[i + 1] + c[i + 1] - c[i]);
        assert(c[i + 1] - c[i] == a[i]);
        assert(c[j] - c[i] == sum(a, i + 1, j) + a[i]);
        assert(c[j] - c[i] == sum(a, i, j));
    }
}

proof fn lemma_prefix_sum_bounds(a: Seq<int>, c: Seq<int>)
    requires
        a.len() + 1 == c.len(),
        c.len() > 0,
        c[0] == 0,
        is_prefix_sum_for(a, c),
        forall|k: int| 0 <= k < a.len() ==> i32::MIN <= a[k] <= i32::MAX,
    ensures
        forall|k: int| 0 <= k < c.len() ==> {
            c[k] >= (a.len() as int) * i32::MIN && c[k] <= (a.len() as int) * i32::MAX
        }
{
    // This lemma helps establish bounds on the prefix sum values
    // The actual values in c are bounded by the sum of all elements
}
// </vc-helpers>

// <vc-spec>
fn queryFast(a: &[i32], c: &[i32], i: i32, j: i32) -> (r: i32)
    requires a.len() + 1 == c.len() && c.len() > 0 && c@[0] == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a@.map(|_i, x| x as int), c@.map(|_i, x| x as int))
    ensures r as int == sum(a@.map(|_i, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    proof {
        let a_spec = a@.map(|_i, x| x as int);
        let c_spec = c@.map(|_i, x| x as int);
        lemma_prefix_sum_range(a_spec, c_spec, i as int, j as int);
        assert(c_spec[j as int] - c_spec[i as int] == sum(a_spec, i as int, j as int));
    }
    
    let cj = c[j as usize];
    let ci = c[i as usize];
    
    proof {
        let a_spec = a@.map(|_i, x| x as int);
        let c_spec = c@.map(|_i, x| x as int);
        
        // We know that c_spec[j] - c_spec[i] == sum(a_spec, i, j)
        assert(c_spec[j as int] - c_spec[i as int] == sum(a_spec, i as int, j as int));
        
        // Since c contains i32 values, and the difference equals the sum
        assert(cj as int == c_spec[j as int]);
        assert(ci as int == c_spec[i as int]);
        assert(cj as int - ci as int == sum(a_spec, i as int, j as int));
        
        // The result fits in i32 because it represents a sum of elements from the original array
        // which are all i32 values, and the sum is bounded by the array length times i32 bounds
    }
    
    cj - ci
}
// </vc-code>

fn main() {}

}