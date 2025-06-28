use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RotateRight(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires
        n >= 0
    ensures
        r.len() == l.len(),
        forall i :: 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index((i - n + l.len()) % l.len())
{
    if l.len() == 0 {
        return l;
    }
    
    let effective_n = n % l.len();
    let split_point = (l.len() - effective_n) % l.len();
    
    let left_part = l.subrange(0, split_point);
    let right_part = l.subrange(split_point, l.len() as int);
    
    right_part + left_part
}

}