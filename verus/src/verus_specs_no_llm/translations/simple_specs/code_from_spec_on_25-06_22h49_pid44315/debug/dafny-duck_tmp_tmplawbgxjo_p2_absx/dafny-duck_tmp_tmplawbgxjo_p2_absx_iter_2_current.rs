use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn absx(x: Vec<int>) -> (y: Vec<int>)
    ensures
        y.len() == x.len(),
        forall|i: int| 0 <= i < y.len() ==> y.spec_index(i) == abs(x.spec_index(i))
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == abs(x.spec_index(j))
    {
        let abs_val = if x[i] >= 0 { x[i] } else { -x[i] };
        result.push(abs_val);
        i += 1;
    }
    
    result
}

}