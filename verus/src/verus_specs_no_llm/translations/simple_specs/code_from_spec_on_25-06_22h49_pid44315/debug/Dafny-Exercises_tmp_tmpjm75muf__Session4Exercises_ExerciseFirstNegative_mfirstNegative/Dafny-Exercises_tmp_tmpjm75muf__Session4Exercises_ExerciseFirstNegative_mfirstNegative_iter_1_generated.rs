use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u| 0 <= u < s.len() ==> s.spec_index(u) >= 0
}

fn mfirstNegative(v: Vec<int>) -> (b: bool, i: int)
    ensures
        b <==> exists |k| 0 <= k < v.len() && v.spec_index(k) < 0,
        b ==> 0 <= i < v.len() && v.spec_index(i) < 0 && positive(v@.spec_index(0..i as nat))
{
    let mut index = 0;
    
    while index < v.len()
        invariant
            0 <= index <= v.len(),
            forall |j| 0 <= j < index ==> v.spec_index(j) >= 0,
    {
        if v[index] < 0 {
            return (true, index as int);
        }
        index += 1;
    }
    
    return (false, 0);
}

}