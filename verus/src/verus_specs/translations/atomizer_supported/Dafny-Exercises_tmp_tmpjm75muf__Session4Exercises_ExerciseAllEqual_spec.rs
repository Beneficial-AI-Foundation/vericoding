use vstd::prelude::*;

verus! {

spec fn allEqual(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}

proof fn equivalenceNoOrder(s: Seq<int>)
    ensures allEqual(s) <==> (forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] == s[j])
{
}

proof fn equivalenceEqualtoFirst(s: Seq<int>)
    requires s.len() != 0
    ensures allEqual(s) <==> (forall|i: int| 0 <= i < s.len() ==> s[0] == s[i])
{
}

proof fn equivalenceContiguous(s: Seq<int>)
    ensures (allEqual(s) ==> (forall|i: int| 0 <= i < s.len() - 1 ==> s[i] == s[i + 1]))
    ensures (allEqual(s) <== (forall|i: int| 0 <= i < s.len() - 1 ==> s[i] == s[i + 1]))
{
}

pub fn mallEqual1(v: &[i32]) -> (b: bool)
    ensures b == allEqual(v@)
{
}

pub fn mallEqual2(v: &[i32]) -> (b: bool)
    ensures b == allEqual(v@)
{
}

pub fn mallEqual3(v: &[i32]) -> (b: bool)
    ensures b == allEqual(v@)
{
}

pub fn mallEqual4(v: &[i32]) -> (b: bool)
    ensures b == allEqual(v@)
{
}

pub fn mallEqual5(v: &[i32]) -> (b: bool)
    ensures b == allEqual(v@)
{
}

}