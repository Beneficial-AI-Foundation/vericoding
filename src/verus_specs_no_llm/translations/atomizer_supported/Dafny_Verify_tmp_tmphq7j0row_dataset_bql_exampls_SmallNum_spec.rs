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

fn add_small_numbers(a: Vec<int>, n: int, max: int) -> (r: int)
    requires
        n > 0;,
        n <= a.len();,
        (forall i: int :: 0 <= i && i < n ==> a.spec_index(i) <= max);
    ensures
        r <= max * n;
{
    return 0;
}

}