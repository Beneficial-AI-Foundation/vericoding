pub fn mergeSimple(a1: Seq<int>, a2: Seq<int>, start: int, end: int, b: &mut Array<int>)
    requires(
        sorted_seq(a1),
        sorted_seq(a2),
        0 <= start <= end <= b.len(),
        a1.len() + a2.len() == end - start + 1,
    )
    ensures(
        sorted_slice(b, start, end),
    )
{
}

pub fn merge(a1: Seq<int>, a2: Seq<int>, start: int, end: int, b: &mut Array<int>)
    requires(
        sorted_seq(a1),
        sorted_seq(a2),
        end - start == a1.len() + a2.len(),
        0 <= start < end < a1.len() && end <= a2.len() < b.len(),
        end < a1.len() && end < a2.len(),
        b.len() == a2.len() + a1.len(),
    )
    ensures(
        sorted_slice(b, start, end),
        merged(a1, a2, b, start, end),
    )
{
}

pub closed spec fn merged(a1: Seq<int>, a2: Seq<int>, b: &Array<int>, start: int, end: int) -> bool
    recommends(
        end - start == a2.len() + a1.len(),
        0 <= start <= end <= b.len(),
    )
{
    a1.to_multiset() + a2.to_multiset() == b.subrange(start, end).to_multiset()
}

pub closed spec fn sorted_slice(a: &Array<int>, start: int, end: int) -> bool
    recommends(0 <= start <= end <= a.len())
{
    forall|i: int, j: int| start <= i <= j < end ==> a[i] <= a[j]
}

pub closed spec fn sorted_seq(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

pub closed spec fn sorted(a: &Array<int>) -> bool
{
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}