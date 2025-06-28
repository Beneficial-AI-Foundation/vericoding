use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementWiseModulo(a: Vec<int>, b: Vec<int>) -> (result: Vec<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b.spec_index(i) != 0
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) % b.spec_index(i)
{
    let mut result = Vec::new();
    let mut index: usize = 0;
    
    while index < a.len()
        invariant
            0 <= index <= a.len(),
            a.len() == b.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) % b.spec_index(i),
            forall|i: int| 0 <= i < b.len() ==> b.spec_index(i) != 0
    {
        assert(index < a.len());
        assert(index < b.len());
        assert(b.spec_index(index as int) != 0);
        
        let mod_value = a[index] % b[index];
        result.push(mod_value);
        
        assert(result.spec_index(index as int) == a.spec_index(index as int) % b.spec_index(index as int));
        
        index += 1;
    }
    
    result
}

}