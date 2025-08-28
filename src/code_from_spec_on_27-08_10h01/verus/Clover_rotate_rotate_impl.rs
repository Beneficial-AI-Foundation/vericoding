use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn mod_add(i: int, offset: int, len: int) -> int
{
    (i + offset) % len
}

proof fn mod_add_bounds(i: int, offset: int, len: int)
    requires 
        0 <= i < len,
        len > 0
    ensures 
        0 <= mod_add(i, offset, len) < len
{
    let result = (i + offset) % len;
    assert(result >= 0);
    assert(result < len);
}

proof fn index_bounds(i: usize, offset: usize, len: usize)
    requires 
        i < len,
        len > 0
    ensures 
        (i as int + offset as int) % len as int < len as int,
        (i as int + offset as int) % len as int >= 0
{
    assert((i as int + offset as int) % len as int < len as int);
    assert((i as int + offset as int) % len as int >= 0);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn rotate(a: &[i32], offset: usize) -> (result: Vec<i32>)
    requires 
        offset >= 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[(i + offset as int) % a.len() as int],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let len = a.len();
    
    for i in 0..len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[(j + offset as int) % len as int]
    {
        proof {
            index_bounds(i, offset, len);
        }
        let index = ((i as int + offset as int) % len as int) as usize;
        result.push(a[index]);
    }
    
    result
}
// </vc-code>

fn main() {}

}