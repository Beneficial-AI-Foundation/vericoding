use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int| 0<=u<s.len() ==> s.spec_index(u)>=0
}

fn mpositive3(v: Vec<int>) -> (b: bool)
    ensures
        b==positive(v@.spec_index(0..v.len() as int))
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |u: int| 0 <= u < i ==> v@.spec_index(u) >= 0,
    {
        if v[i] < 0 {
            return false;
        }
        i += 1;
    }
    return true;
}

}