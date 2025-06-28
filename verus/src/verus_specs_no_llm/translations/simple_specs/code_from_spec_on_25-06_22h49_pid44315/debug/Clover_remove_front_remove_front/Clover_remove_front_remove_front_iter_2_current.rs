use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn remove_front(a: Vec<int>) -> (c: Vec<int>)
    requires
        a.len() > 0
    ensures
        a@.subrange(1, a@.len() as int) =~= c@
{
    let mut c = Vec::new();
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            i <= a.len(),
            c@.len() == i - 1,
            forall|j: int| 0 <= j < c@.len() ==> c@[j] == a@[j + 1]
    {
        c.push(a[i]);
        i += 1;
    }
    
    assert(c@ =~= a@.subrange(1, a@.len() as int));
    c
}

}