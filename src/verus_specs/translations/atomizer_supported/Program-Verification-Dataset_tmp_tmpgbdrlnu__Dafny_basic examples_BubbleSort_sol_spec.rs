pub fn sorted_between(a: &[int], from: usize, to: usize) -> bool
    requires(
        from <= to,
        to <= a.len(),
    )
{
    forall|i: usize, j: usize| from <= i < j < to && 0 <= i < j < a.len() ==> a[i] <= a[j]
}

pub fn sorted(a: &[int]) -> bool
{
    sorted_between(a, 0, a.len())
}

pub fn bubbleSort(a: &mut [int])
    requires(
        a.len() > 0,
    )
    ensures(
        sorted(a),
        multiset(old(a).to_seq()) == multiset(a.to_seq()),
    )
{
}