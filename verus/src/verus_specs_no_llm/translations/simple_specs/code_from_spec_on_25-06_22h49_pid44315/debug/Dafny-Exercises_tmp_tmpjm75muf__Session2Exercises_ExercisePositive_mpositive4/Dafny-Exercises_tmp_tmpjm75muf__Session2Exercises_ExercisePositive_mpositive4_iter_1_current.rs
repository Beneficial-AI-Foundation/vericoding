use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int| 0<=u<s.len() ==> s.spec_index(u)>=0
}

fn mpositive4(v: Vec<int>) -> (b: bool)
    ensures
        b==positive(v@)
{
    for i in 0..v.len()
        invariant
            forall |u: int| 0<=u<i ==> v@.spec_index(u)>=0
    {
        if v[i] < 0 {
            return false;
        }
    }
    return true;
}

}