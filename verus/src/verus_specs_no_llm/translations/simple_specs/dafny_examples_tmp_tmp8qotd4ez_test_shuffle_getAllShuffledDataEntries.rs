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
 
method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
 // requires m_dataEntries != null
 // ensures result != null
 ensures result.Length == m_dataEntries.Length
 ensures multiset(result[..]) == multiset(m_dataEntries[..]
    requires
        a <= b,
        m_dataEntries != null
 //
    ensures
        a <= b ==> a <= r <= b


// SPEC
 
method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
 //,
        result != null,
        result.len() == m_dataEntries.len(),
        multiset(result.index(..)) == multiset(m_dataEntries.index(..))
;

proof fn lemma_random(a: int, b: int) -> (r: int)
// requires a <= b
 ensures a <= b ==> a <= r <= b


// SPEC
 
method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
 // requires m_dataEntries != null
 // ensures result != null
 ensures result.Length == m_dataEntries.Length
 ensures multiset(result[..]) == multiset(m_dataEntries[..])
    requires
        a <= b,
        m_dataEntries != null
 //
    ensures
        a <= b ==> a <= r <= b


// SPEC
 
method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
 //,
        result != null,
        result.len() == m_dataEntries.len(),
        multiset(result.index(..)) == multiset(m_dataEntries.index(..))
{
    0
}

}