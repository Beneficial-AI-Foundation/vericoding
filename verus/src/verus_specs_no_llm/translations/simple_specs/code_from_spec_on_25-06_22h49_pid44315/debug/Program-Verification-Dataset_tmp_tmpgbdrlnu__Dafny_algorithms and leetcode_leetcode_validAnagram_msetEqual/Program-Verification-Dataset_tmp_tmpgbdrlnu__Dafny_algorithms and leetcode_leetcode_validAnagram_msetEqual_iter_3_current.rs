use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn msetEqual(s: multiset<char>, t: multiset<char>) -> (equal: bool)
    ensures
        s == t <==> equal
{
    let result = s == t;
    proof {
        // The ensures clause is satisfied by the definition of result
        // result is true iff s == t, which directly establishes the biconditional
    }
    result
}

}