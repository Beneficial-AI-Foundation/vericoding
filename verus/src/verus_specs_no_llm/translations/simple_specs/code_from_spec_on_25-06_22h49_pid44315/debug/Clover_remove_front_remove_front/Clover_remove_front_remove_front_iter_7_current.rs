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
            1 <= i <= a.len(),
            c@.len() == (i - 1) as int,
            c@ =~= a@.subrange(1, i as int)
    {
        c.push(a.index(i));
        i += 1;
    }
    
    c
}

}