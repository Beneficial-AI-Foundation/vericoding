use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
{
    let mut last_pos = 0;
    let mut found = false;
    
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            found ==> (0 <= last_pos < i && a[last_pos as int] == elem),
            found ==> forall|j: int| last_pos < j < i ==> a[j] != elem,
            found <==> exists|j: int| 0 <= j < i && a[j] == elem,
        decreases a.len() - i
    {
        if a[i] == elem {
            last_pos = i;
            found = true;
        }
        i += 1;
    }
    
    last_pos
}

fn main() {}
}