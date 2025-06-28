use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i <= main.len() - sub.len() && sub == main.subrange(i, i + sub.len()))
{
    if sub.len() > main.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= main.len() - sub.len()
        invariant
            0 <= i <= main.len() - sub.len() + 1,
            forall|j: int| 0 <= j < i ==> sub != main.subrange(j, j + sub.len())
    {
        if sub == main.subrange(i as int, i as int + sub.len()) {
            return true;
        }
        i += 1;
    }
    false
}

}