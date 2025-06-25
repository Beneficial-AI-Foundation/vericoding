// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn random(a: int, b: int) -> (r: int)
// requires a <= b
 ensures a <= b ==> a <= r <= b


// SPEC
 
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: Seq<T>)
    requires
        a <= b,
        m_workList.len() > 0
//
    ensures
        a <= b ==> a <= r <= b


// SPEC
 
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T),
        set_of_seq(avoidSet) < set_of_seq(m_workList.spec_index(..)) ==> e !in avoidSet
//,
        avoidSet < m_workList.spec_index(..) ==> e in m_workList.spec_index(..)
{
    return (0, Seq::empty());
}

}