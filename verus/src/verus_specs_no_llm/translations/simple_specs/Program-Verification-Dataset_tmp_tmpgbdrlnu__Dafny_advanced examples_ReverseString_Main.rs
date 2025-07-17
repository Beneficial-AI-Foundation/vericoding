// Translated from Dafny
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
 var a,b,c,d := new char.index(5), new char.index(5), new char.index(5), new char.index(5);
 a.index(0), a.index(1), a.index(2), a.index(3), a.index(4) := 'y', 'a', 'r', 'r', 'a';
 d.index(0), d.index(1), d.index(2), d.index(3), d.index(4) := 'y', 'a', 'r', 'r', 'a';
 b := yarra(a);
 c := yarra(b);
 //assert c.len() > -2;
 //assert d.index(0) == a.index(0);
 //print c; print a
}

}