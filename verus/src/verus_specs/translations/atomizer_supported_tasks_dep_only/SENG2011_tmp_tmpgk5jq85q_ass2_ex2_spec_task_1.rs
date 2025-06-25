spec fn sorted(a: &str, low: int, high: int) -> bool
    requires 0 <= low <= high <= a.len()
{
    forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}

pub fn string3_sort(a: &str) -> (b: String)
    requires a.len() == 3
    ensures sorted(&b, 0, b.len())
    ensures a.len() == b.len()
    ensures multiset{b.chars().nth(0), b.chars().nth(1), b.chars().nth(2)} == multiset{a.chars().nth(0), a.chars().nth(1), a.chars().nth(2)}
{
}