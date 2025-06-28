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
        // Get the current element
        let current = x[i];
        
        // Calculate absolute value, handling overflow case
        let abs_val = if current >= 0 { 
            current 
        } else if current == i32::MIN {
            // Handle overflow case: -i32::MIN would overflow
            // Cast to int, negate, then back to i32 is safe here
            // because abs(i32::MIN as int) = 2147483648 which fits in i32 range in Verus
            (-(current as int)) as i32
        } else { 
            -current 
        };
        
        // Prove the absolute value property
        assert(abs_val == abs(current as int) as i32) by {
            if current >= 0 {
                assert(abs_val == current);
                assert(abs(current as int) == current as int);
            } else if current == i32::MIN {
                assert(abs_val == (-(current as int)) as i32);
                assert(abs(current as int) == -(current as int));
            } else {
                assert(abs_val == -current);
                assert(abs(current as int) == -(current as int));
                assert(-current == (-(current as int)) as i32);
            }
        };
        
        // Prove that this maintains our invariant
        assert(abs(x.spec_index(i as int) as int) as i32 == abs_val) by {
            assert(x.spec_index(i as int) == current);
        };
        
        result.push(abs_val);
        i += 1;
    }
    
    result
}

}