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
        i += 1;
    }
    
    result
}

}