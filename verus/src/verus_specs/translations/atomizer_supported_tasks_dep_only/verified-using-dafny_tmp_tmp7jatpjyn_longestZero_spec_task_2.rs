// ATOM 
fn getSize(i: int, j: int) -> int
{
    j - i + 1    
}

// For a given integer array, let's find the longest subesquence of 0s.
// sz: size, pos: position.   a[pos..(pos+sz)] will be all zeros
// SPEC 

// For a given integer array, let's find the longest subesquence of 0s.
// sz: size, pos: position.   a[pos..(pos+sz)] will be all zeros
pub fn longestZero(a: &[int]) -> (sz: int, pos: int)
    requires(1 <= a.len())
    ensures(|result: (int, int)| {
        let (sz, pos) = result;
        0 <= sz <= a.len() &&
        0 <= pos < a.len() &&
        pos + sz <= a.len() &&
        (forall|i: int| pos <= i < pos + sz ==> a[i] == 0) &&
        (forall|i: int, j: int| (0 <= i < j < a.len() && getSize(i, j) > sz) ==> exists|k: int| i <= k <= j && a[k] != 0)
    })
{
}

// SPEC 

pub fn Main()
{
}