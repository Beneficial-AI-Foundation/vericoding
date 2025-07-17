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

method yarra(arr : array<char>) returns (outarr : array<char>)
requires arr != null && arr.Length > 0
ensures outarr != null && arr.Length == outarr.Length && reversed(arr, outarr) -> bool {
    
}

spec fn spec_yarra(arr: Vec<char>) -> outarr : array<char>
    requires
        arr != null && arr.len() > 0
    ensures
        outarr != null && arr.len() == outarr.len() && reversed(arr,outarr)
;

proof fn lemma_yarra(arr: Vec<char>) -> (outarr: Vec<char>)
    requires
        arr != null && arr.len() > 0
    ensures
        outarr != null && arr.len() == outarr.len() && reversed(arr,outarr)
{
    Vec::new()
}

}