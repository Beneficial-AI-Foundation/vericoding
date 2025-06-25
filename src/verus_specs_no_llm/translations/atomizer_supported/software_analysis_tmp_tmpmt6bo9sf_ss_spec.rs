// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn is_sorted(ss: Seq<int>) -> bool {
    forall i, j: int:: 0 <= i <= j < ss.len() ==> ss[i] <= ss[j]
}
spec fn is_permutation(a: Seq<int>, b: Seq<int>) -> bool {
    a.len() == b.len()  and 
    ((a.len() == 0 and b.len() == 0) |  
    exists i,j : int :: 0<=i<.len()a and  0<=j<.len()b  and a[i] == b[j] and is_permutation(a[0..i] + if i < .len()a then a[i+1..] else [], b[0..j] + if j < .len()b| then  b[j+1..] else []))
}
spec fn is_permutation(a: Seq<int>, b: Seq<int>, j: int :: 0<=i<|a| &&  0<=j<|b|  && a[i] == b[j] && is_permutation(a[0..i] + a[i+1..], b[0..j] + b[j+1..]))
// }

// ATOM 


// predicate is_permutation(a: Seq<int>, b: Seq<int>, j: int :: 0<=i<|a| &&  0<=j<|b|  && a[i] == b[j] && is_permutation(a[0..i] + a[i+1..], b[0..j] + b[j+1..]))
// }

predicate is_permutation2(a: Seq<int>, b: Seq<int>) -> bool {
    multiset(a) == multiset(b)
}

fn find_min_index(a: Vec<int>, s: int, e: int) -> (min_i: int)
    requires a.len() > 0,
             0 <= s < a.len(),
             e <= a.len(),
             e > s
    ensures min_i >= s,
            min_i < e,
            forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
}

}