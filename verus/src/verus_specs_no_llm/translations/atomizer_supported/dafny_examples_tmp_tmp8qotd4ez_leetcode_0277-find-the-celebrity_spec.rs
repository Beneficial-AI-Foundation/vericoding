// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn knows(a: int, b: int)
// ATOM 

predicate isCelebrity(n : int, i: int)
requires n >= 0 && 0 <= i < n;
{
    forall j :: 0 <= j < n && i != j ==> knows(j, i) && !knows(i, j)
}


// ATOM 

lemma knowerCannotBeCelebrity(n: int, i: int)
requires n >= 0 && 0 <= i < n
ensures (exists j :: 0 <= j < n && j != i && knows(i, j)) ==> !isCelebrity(n, i)
{}


// ATOM 

ghost method isCelebrityP(n: int, i: int) returns (r : bool)
requires n >= 0 && 0 <= i < n;
ensures r <==> isCelebrity(n, i);
{
    var j: = 0;
    r := true;
    while j < n
    {
        if j != i {
            if !knows(j, i) || knows(i, j) -> bool {
    return false
}

}