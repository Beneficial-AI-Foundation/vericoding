// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn rotate(a: Vec<int>, offset: int) -> (b: Vec<int>)
    requires
        0<=offset
    ensures
        b.len()==a.len(),
        forall i::0<=i<a.len() ==> b.spec_index(i)==a.spec_index((i+offset)%a.len())
{
    if a.len() == 0 {
        return a;
    }
    
    let mut result = Vec::new();
    let len = a.len();
    let effective_offset = offset % len;
    
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall j::0<=j<i ==> result.spec_index(j)==a.spec_index((j+offset)%len)
    {
        let source_index = (i + effective_offset) % len;
        result.push(a[source_index]);
        i += 1;
    }
    
    result
}

}