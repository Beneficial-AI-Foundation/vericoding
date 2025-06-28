use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures
        forall|x: char| c.contains(x) <==> (exists|j: int| 0 <= j < a.len() && a[j] == x && b.contains(x))
{
    let mut result: Set<char> = Set::empty();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: char| result.contains(x) <==> (exists|j: int| 0 <= j < i && a[j] == x && b.contains(x)),
    {
        if b.contains(a[i]) {
            result = result.insert(a[i]);
        }
        i = i + 1;
    }
    
    result
}

}