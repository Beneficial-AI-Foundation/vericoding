use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn aba(a: Vec<int>) -> (b: Vec<int>)
    ensures
        a.len() == b.len(), // needed for next line,
        forall|x: int| 0 <= x < b.len() ==> b.spec_index(x) == abs(a.spec_index(x))
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == abs(a.spec_index(j))
    {
        let val = a[i];
        let abs_val = if val < 0 { -val } else { val };
        result.push(abs_val);
        
        // Proof that abs_val equals abs(a.spec_index(i as int))
        assert(abs_val == abs(a.spec_index(i as int)));
        
        i += 1;
    }
    
    result
}

}