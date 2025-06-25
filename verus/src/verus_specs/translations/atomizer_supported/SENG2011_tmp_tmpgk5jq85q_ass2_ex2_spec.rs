pub spec fn sorted(a: Seq<char>, low: int, high: int) -> bool
{
    &&& 0 <= low <= high <= a.len()
    &&& forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}

pub fn string3_sort(a: Seq<char>) -> (b: Seq<char>)
    requires(a.len() == 3)
    ensures(sorted(b, 0, b.len()))
    ensures(a.len() == b.len())
    ensures(multiset![b[0], b[1], b[2]] == multiset![a[0], a[1], a[2]])
{
}

pub fn check()
{
}