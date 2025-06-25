// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CanyonSearch(a: Vec<int>, b: Vec<int>) -> (d: nat)
    requires
        a.len() !=0 && b.len()!=0,
        forall i,j :: 0<=i<j<a.len() ==> a.spec_index(i)<=a.spec_index(j),
        forall i,j :: 0<=i<j<b.len() ==> b.spec_index(i)<=b.spec_index(j)
    ensures
        exists i,j:: 0<=i<a.len() && 0<=j<b.len() && d==if a.spec_index(i) < b.spec_index(j) then (b.spec_index(j)-a.spec_index(i)) else (a.spec_index(i)-b.spec_index(j)),
        forall i,j:: 0<=i<a.len() && 0<=j<b.len() ==> d<=if a.spec_index(i) < b.spec_index(j) then (b.spec_index(j)-a.spec_index(i)) else (a.spec_index(i)-b.spec_index(j))
{
    return 0;
}

}