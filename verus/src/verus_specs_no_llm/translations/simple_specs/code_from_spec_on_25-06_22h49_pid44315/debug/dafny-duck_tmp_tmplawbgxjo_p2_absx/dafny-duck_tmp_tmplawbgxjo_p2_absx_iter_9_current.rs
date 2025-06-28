use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn absx(x: Vec<i32>) -> (y: Vec<i32>)
    ensures
        y.len() == x.len(),
        forall|i: int| 0 <= i < y.len() ==> y.spec_index(i) == abs(x.spec_index(i) as int) as i32
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == abs(x.spec_index(j) as int) as i32
    {
        let current = x[i];
        
        // Calculate absolute value in executable code
        let abs_val = if current >= 0 { current } else { -current };
        
        result.push(abs_val);
        
        // Proof that the invariant is maintained
        proof {
            assert(result.len() == i + 1);
            assert(result.spec_index(i as int) == abs_val);
            assert(abs_val == abs(current as int) as i32);
            assert(current == x.spec_index(i as int));
            assert(abs_val == abs(x.spec_index(i as int) as int) as i32);
        }
        
        i += 1;
    }
    
    // Final proof that postconditions are satisfied
    proof {
        assert(i == x.len());
        assert(result.len() == x.len());
    }
    
    result
}

}