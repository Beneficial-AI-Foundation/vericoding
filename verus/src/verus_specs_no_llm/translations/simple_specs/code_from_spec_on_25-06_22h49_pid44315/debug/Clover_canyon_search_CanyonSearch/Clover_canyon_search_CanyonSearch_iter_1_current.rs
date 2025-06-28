// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CanyonSearch(a: Vec<int>, b: Vec<int>) -> (d: nat)
    requires
        a.len() != 0 && b.len() != 0,
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j),
        forall|i: int, j: int| 0 <= i < j < b.len() ==> b.spec_index(i) <= b.spec_index(j)
    ensures
        exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && d == if a.spec_index(i) < b.spec_index(j) { (b.spec_index(j) - a.spec_index(i)) as nat } else { (a.spec_index(i) - b.spec_index(j)) as nat },
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> d <= if a.spec_index(i) < b.spec_index(j) { (b.spec_index(j) - a.spec_index(i)) as nat } else { (a.spec_index(i) - b.spec_index(j)) as nat }
{
    let mut min_diff: nat = if a[0] < b[0] { (b[0] - a[0]) as nat } else { (a[0] - b[0]) as nat };
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < a.len() && j < b.len()
        invariant
            i < a.len(),
            j < b.len(),
            exists|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && min_diff == if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat },
            forall|x: int, y: int| 0 <= x <= i && 0 <= y <= j ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat }
    {
        let curr_diff = if a[i] < b[j] { (b[j] - a[i]) as nat } else { (a[i] - b[j]) as nat };
        
        if curr_diff < min_diff {
            min_diff = curr_diff;
        }
        
        if a[i] < b[j] {
            i = i + 1;
        } else {
            j = j + 1;
        }
    }
    
    // Handle remaining elements
    while i < a.len()
        invariant
            j == b.len(),
            i <= a.len(),
            exists|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && min_diff == if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat },
            forall|x: int, y: int| (0 <= x < i && 0 <= y < b.len()) ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat }
    {
        let curr_diff = if a[i] < b[b.len() - 1] { (b[b.len() - 1] - a[i]) as nat } else { (a[i] - b[b.len() - 1]) as nat };
        
        if curr_diff < min_diff {
            min_diff = curr_diff;
        }
        
        i = i + 1;
    }
    
    while j < b.len()
        invariant
            i == a.len(),
            j <= b.len(),
            exists|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && min_diff == if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat },
            forall|x: int, y: int| (0 <= x < a.len() && 0 <= y < j) ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat }
    {
        let curr_diff = if a[a.len() - 1] < b[j] { (b[j] - a[a.len() - 1]) as nat } else { (a[a.len() - 1] - b[j]) as nat };
        
        if curr_diff < min_diff {
            min_diff = curr_diff;
        }
        
        j = j + 1;
    }
    
    min_diff
}

}