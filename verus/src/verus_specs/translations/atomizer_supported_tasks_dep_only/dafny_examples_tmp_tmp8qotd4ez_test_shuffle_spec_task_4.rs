pub fn random(a: int, b: int) -> (r: int)
    ensures(a <= b ==> a <= r && r <= b)
{
}

spec fn set_of_seq<T>(s: Seq<T>) -> Set<T>
{
    Set::new(|x: T| s.contains(x))
}

pub fn getRandomDataEntry<T>(m_workList: &[T], avoidSet: Seq<T>) -> (e: T)
    requires(m_workList.len() > 0)
{
}