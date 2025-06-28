use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn msetEqual(s: multiset<char>, t: multiset<char>) -> (equal: bool)
    ensures
        s == t <==> equal
{
    s == t
}

}

The implementation is straightforward - I directly compare the two multisets using the `==` operator. In Verus, multisets have built-in equality comparison that checks if they contain the same elements with the same multiplicities. The postcondition `s == t <==> equal` ensures that the function returns `true` if and only if the multisets are equal, which is exactly what the direct comparison `s == t` provides.