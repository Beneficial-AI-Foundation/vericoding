pub fn random(a: int, b: int) -> (r: int)
    ensures(a <= b ==> a <= r && r <= b)
{
}

proof fn eqMultiset_t<T>(t: T, s1: Seq<T>, s2: Seq<T>)
    requires(s1.to_multiset() == s2.to_multiset())
    ensures(s1.contains(t) <==> s2.contains(t))
{
}

proof fn eqMultiset<T>(s1: Seq<T>, s2: Seq<T>)
    requires(s1.to_multiset() == s2.to_multiset())
    ensures(forall|t: T| s1.contains(t) <==> s2.contains(t))
{
}

pub fn swap<T>(a: &mut [T], i: int, j: int)
    requires(0 <= i < old(a).len() && 0 <= j < old(a).len())
    ensures(a[i as int] == old(a)[j as int])
    ensures(a[j as int] == old(a)[i as int])
    ensures(forall|m: int| 0 <= m < a.len() && m != i && m != j ==> a[m] == old(a)[m])
    ensures(a@.to_multiset() == old(a)@.to_multiset())
{
}

pub fn getAllShuffledDataEntries<T>(m_dataEntries: &[T]) -> (result: Vec<T>)
    ensures(result@.len() == m_dataEntries@.len())
    ensures(result@.to_multiset() == m_dataEntries@.to_multiset())
{
}

spec fn set_of_seq<T>(s: Seq<T>) -> Set<T>
{
    Set::new(|x: T| s.contains(x))
}

proof fn in_set_of_seq<T>(x: T, s: Seq<T>)
    ensures(s.contains(x) <==> set_of_seq(s).contains(x))
{
}

proof fn subset_set_of_seq<T>(s1: Seq<T>, s2: Seq<T>)
    requires(set_of_seq(s1).subset_of(set_of_seq(s2)))
    ensures(forall|x: T| s1.contains(x) ==> s2.contains(x))
{
}

pub fn getRandomDataEntry<T>(m_workList: &[T], avoidSet: Seq<T>) -> (e: T)
    requires(m_workList@.len() > 0)
{
}