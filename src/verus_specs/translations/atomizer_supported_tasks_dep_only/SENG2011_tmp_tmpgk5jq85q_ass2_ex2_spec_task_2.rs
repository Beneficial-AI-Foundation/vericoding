// verifies
// check that string between indexes low and high-1 are sorted
// ATOM 
// verifies
// check that string between indexes low and high-1 are sorted
spec fn Sorted(a: string, low: int, high: int) -> bool
    requires 0 <= low <= high <= a.len()
{ 
    forall |j: int, k: int| low <= j < k < high ==> a[j] <= a[k] 
}

// SPEC 

pub fn String3Sort(a: string) -> (b: string)
    requires a.len() == 3
    ensures Sorted(b, 0, b.len())
    ensures a.len() == b.len()
    ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]}
{
}

// SPEC 

pub fn check()
{
}