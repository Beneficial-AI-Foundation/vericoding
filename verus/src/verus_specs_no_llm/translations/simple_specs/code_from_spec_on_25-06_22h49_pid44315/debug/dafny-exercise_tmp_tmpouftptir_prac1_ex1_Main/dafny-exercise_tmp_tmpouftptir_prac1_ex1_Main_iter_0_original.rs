// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn acheck(a: Vec<int>, n: int)
reads a
requires n >= 1
{
	a.Length % 2 == 0 && 
	forall i :: 0 <= i < a.Length ==> 
		if i % n == 0 then a[i] == 0 else a[i] != 0
}


// SPEC

method Main() -> bool {
    var arr: array<int> := new int[][0,42,0,42];
	var res := acheck(arr, 2);
	
	arr := new int[][];
	res := acheck(arr, 2);
	
	arr := new int[][0,4,2,0];
	res := acheck(arr, 2)
}

}