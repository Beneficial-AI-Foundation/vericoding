// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_random(a: int, b: int) -> r: int)
// requires a <= b
 ensures a <= b ==> a <= r <= b


// SPEC
 
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T
    requires
        a <= b,
        m_workList.len() > 0
//
    ensures
        a <= b ==> a <= r <= b


// SPEC
 
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T),
        set_of_seq(avoidSet) < set_of_seq(m_workList.index(..)) ==> e !in avoidSet
//,
        avoidSet < m_workList.index(..) ==> e in m_workList.index(..)
;

proof fn lemma_random(a: int, b: int) -> (r: int)
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
        set_of_seq(avoidSet) < set_of_seq(m_workList.index(..)) ==> e !in avoidSet
//,
        avoidSet < m_workList.index(..) ==> e in m_workList.index(..)
{
    (0, Seq::empty())
}

}