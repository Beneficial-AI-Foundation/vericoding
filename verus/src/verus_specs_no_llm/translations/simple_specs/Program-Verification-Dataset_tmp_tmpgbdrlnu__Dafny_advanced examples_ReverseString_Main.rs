// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn reversed(arr: Vec<char>, outarr: Vec<char>, outarr
{
 forall k: : 0<=k<=arr.Length-1 ==> outarr[k] == arr[(arr.Length-1-k)]
}


// SPEC

method Main() -> bool {
    var s := ['a','b','a','b','a','b','a','b','a','b','a','b'];
 var a,b,c,d := new char.spec_index(5), new char.spec_index(5), new char.spec_index(5), new char.spec_index(5);
 a.spec_index(0), a.spec_index(1), a.spec_index(2), a.spec_index(3), a.spec_index(4) := 'y', 'a', 'r', 'r', 'a';
 d.spec_index(0), d.spec_index(1), d.spec_index(2), d.spec_index(3), d.spec_index(4) := 'y', 'a', 'r', 'r', 'a';
 b := yarra(a);
 c := yarra(b);
 //assert c.len() > -2;
 //assert d.spec_index(0) == a.spec_index(0);
 //print c; print a
}

}