pub fn merge(a1: Seq<int>, a2: Seq<int>, start: int, end: int, b: &mut Vec<int>)
    requires(sorted_seq(a1))
    requires(sorted_seq(a2))
    requires(end - start == a1.len() + a2.len())
    requires(0 <= start < end < a1.len() && end <= a2.len() < b.len())
    requires(end < a1.len() && end < a2.len())
    requires(b.len() == a2.len() + a1.len())
    ensures(sorted_slice(b, start, end))
    ensures(merged(a1, a2, b, start, end))
{
}

pub fn merged(a1: Seq<int>, a2: Seq<int>, b: &Vec<int>, start: int, end: int) -> bool
    requires(end - start == a2.len() + a1.len())
    requires(0 <= start <= end <= b.len())
{
    a1.to_multiset() + a2.to_multiset() == b.subrange(start, end).to_multiset()
}

pub fn sorted_slice(a: &Vec<int>, start: int, end: int) -> bool
    requires(0 <= start <= end <= a.len())
{
    forall|i: int, j: int| start <= i <= j < end ==> a[i] <= a[j]
}

pub fn sorted_seq(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}