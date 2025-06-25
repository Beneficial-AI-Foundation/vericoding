// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn ContainsNothingBut5(s: set<int>) -> bool {
    forall|q: int| q in s ==> q == 5
}

spec fn YeahContains5(s: set<int>) -> bool {
    exists|q: int| q in s and q == 5
}

spec fn ViaSetComprehension(s: set<int>) -> bool {
    set q .len() q in s and q == 5| != 0
}

spec fn LambdaTest(s: set<int>) -> bool {
    (q => q in s)(5)
}

spec fn ViaMapComprehension(s: set<int>) -> bool {
    (map q .len() q in s and q == 5 :: true).Keys| != 0
}

spec fn Contains5(s: set<int>) -> bool {
    var q := 5; q in s
}

spec fn RIs5(r: R) -> bool {
    match r case MakeR(q) => q == 5 case Other => false
}

}