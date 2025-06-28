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
    
    // Process all pairs by advancing through both arrays
    while i < a.len() && j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            i < a.len() || j < b.len(),
            exists|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && min_diff == if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat },
            forall|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat }
    {
        let curr_diff = if a[i] < b[j] { (b[j] - a[i]) as nat } else { (a[i] - b[j]) as nat };
        
        if curr_diff < min_diff {
            min_diff = curr_diff;
        }
        
        // Move the pointer for the smaller element to potentially find a closer match
        if a[i] <= b[j] {
            i = i + 1;
        } else {
            j = j + 1;
        }
    }
    
    // If we haven't processed all elements, we need to check remaining pairs
    let mut i_final = 0;
    while i_final < a.len()
        invariant
            i_final <= a.len(),
            exists|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && min_diff == if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat },
            forall|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat }
    {
        let mut j_inner = 0;
        while j_inner < b.len()
            invariant
                j_inner <= b.len(),
                i_final < a.len(),
                exists|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && min_diff == if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat },
                forall|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() ==> min_diff <= if a.spec_index(x) < b.spec_index(y) { (b.spec_index(y) - a.spec_index(x)) as nat } else { (a.spec_index(x) - b.spec_index(y)) as nat }
        {
            let curr_diff = if a[i_final] < b[j_inner] { (b[j_inner] - a[i_final]) as nat } else { (a[i_final] - b[j_inner]) as nat };
            
            if curr_diff < min_diff {
                min_diff = curr_diff;
            }
            
            j_inner = j_inner + 1;
        }
        i_final = i_final + 1;
    }
    
    min_diff
}

}