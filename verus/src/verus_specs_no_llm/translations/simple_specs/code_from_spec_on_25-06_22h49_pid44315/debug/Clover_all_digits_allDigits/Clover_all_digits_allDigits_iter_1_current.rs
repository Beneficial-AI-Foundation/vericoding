use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn allDigits(s: String) -> (result: bool)
    ensures
        result <==> (forall i :: 0 <= i < s.len() ==> s.spec_index(i) in "0123456789")
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall j :: 0 <= j < i ==> s.spec_index(j) in "0123456789"
    {
        let c = s.spec_index(i);
        if !(c in "0123456789") {
            return false;
        }
        i = i + 1;
    }
    return true;
}

}