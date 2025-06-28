use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SplitStringIntoChars(s: Seq<char>) -> (v: Seq<char>)
    requires
        s.len() <= usize::MAX
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> v.spec_index(i) == s.spec_index(i)
{
    s
}

}