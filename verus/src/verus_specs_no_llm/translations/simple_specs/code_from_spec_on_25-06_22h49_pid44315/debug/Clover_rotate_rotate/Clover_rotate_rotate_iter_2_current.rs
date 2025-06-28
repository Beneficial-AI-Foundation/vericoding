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
    let effective_offset = offset % (len as int);
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            len > 0,
            effective_offset == offset % (len as int),
            forall j: int :: 0<=j<i ==> result.spec_index(j)==a.spec_index((j+effective_offset)%(len as int))
    {
        let source_index = ((i as int) + effective_offset) % (len as int);
        result.push(a[source_index]);
        i += 1;
    }
    
    result
}

}