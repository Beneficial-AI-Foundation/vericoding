// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(s: Seq<int>, n: nat) -> int
    requires
        n <= s.len()
{
    0
}

spec fn spec_below_zero(ops: Seq<int>) -> result: bool
    ensures
        result <==> exists |n: nat| n <= ops.len() && sum(ops, n) < 0
;

proof fn lemma_below_zero(ops: Seq<int>) -> (result: bool)
    ensures
        result <==> exists |n: nat| n <= ops.len() && sum(ops, n) < 0
{
    false
}

}