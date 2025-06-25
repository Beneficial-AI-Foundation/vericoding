pub fn random(a: int, b: int) -> (r: int)
    ensures(a <= b ==> a <= r && r <= b)
{
}

pub fn swap<T>(a: &mut Vec<T>, i: usize, j: usize)
    requires(i < a.len() && j < a.len())
    ensures(a[i as int] == old(a)[j as int])
    ensures(a[j as int] == old(a)[i as int])
    ensures(forall|m: int| 0 <= m < a.len() && m != i && m != j ==> a[m] == old(a)[m])
    ensures(a@.to_multiset() == old(a)@.to_multiset())
{
}

pub fn getAllShuffledDataEntries<T>(m_dataEntries: &Vec<T>) -> (result: Vec<T>)
    ensures(result.len() == m_dataEntries.len())
    ensures(result@.to_multiset() == m_dataEntries@.to_multiset())
{
}