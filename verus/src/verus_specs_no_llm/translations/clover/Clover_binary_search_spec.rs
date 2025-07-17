// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_BinarySearch(a: Vec<int>, key: int) -> n: int
    requires
        forall |i: int, j: int| 0<=i<j<a.len() ==> a.index(i)<=a.index(j)
    ensures
        0<= n <=a.len(),
        forall |i: int| 0<= i < n ==> a.index(i) < key,
        n == a.len() ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) < key,
        forall |i: int| n<= i < a.len() ==> a.index(i)>=key
;

proof fn lemma_BinarySearch(a: Vec<int>, key: int) -> (n: int)
    requires
        forall |i: int, j: int| 0<=i<j<a.len() ==> a.index(i)<=a.index(j)
    ensures
        0<= n <=a.len(),
        forall |i: int| 0<= i < n ==> a.index(i) < key,
        n == a.len() ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) < key,
        forall |i: int| n<= i < a.len() ==> a.index(i)>=key
{
    0
}

}