use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountIdenticalPositions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: int)
    requires
        a.len() == b.len() && b.len() == c.len()
    ensures
        count >= 0,
        count == (set|i: int| 0 <= i < a.len() && a.spec_index(i) == b.spec_index(i) && b.spec_index(i) == c.spec_index(i)).len()
{
    let mut count = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count >= 0,
            count == (set|j: int| 0 <= j < i && a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j)).len(),
            a.len() == b.len() && b.len() == c.len()
    {
        let old_set = set|j: int| 0 <= j < i && a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j);
        let new_set = set|j: int| 0 <= j < i + 1 && a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j);
        
        if a.spec_index(i) == b.spec_index(i) && b.spec_index(i) == c.spec_index(i) {
            // Prove that adding element i increases the set size by 1
            assert(new_set == old_set.insert(i));
            assert(!old_set.contains(i)); // i is not in the old set since old set only contains j < i
            count = count + 1;
        } else {
            // Prove that not adding element i keeps the set size the same
            assert(new_set == old_set);
        }
        i = i + 1;
    }
    
    count
}

}