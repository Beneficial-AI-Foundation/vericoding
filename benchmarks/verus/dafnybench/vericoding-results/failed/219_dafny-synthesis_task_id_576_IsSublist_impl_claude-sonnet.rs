use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_subrange_equality(sub: Seq<int>, main: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= main.len(),
        sub.len() == end - start,
        forall|k: int| 0 <= k < sub.len() ==> sub[k] == #[trigger] main[start + k]
    ensures
        sub =~= main.subrange(start, end)
{
    assert forall|k: int| 0 <= k < sub.len() implies sub[k] == main.subrange(start, end)[k] by {
        assert(main.subrange(start, end)[k] == main[start + k]);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
// </vc-spec>
// <vc-code>
{
    if sub.len() == 0 {
        assert(sub =~= main.subrange(0, 0));
        return true;
    }
    
    if sub.len() > main.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= main.len() - sub.len()
        invariant
            0 <= i <= main.len() - sub.len() + 1,
            forall|k: int| 0 <= k < i ==> !exists|j: int| j == k + sub.len() && sub =~= #[trigger] main.subrange(k, j)
    {
        let mut j: usize = 0;
        let mut matches = true;
        
        while j < sub.len()
            invariant
                0 <= j <= sub.len(),
                matches == forall|k: int| 0 <= k < j ==> sub[k] == #[trigger] main[(i + k) as int]
        {
            if main[i + j] != sub[j] {
                matches = false;
                break;
            }
            j = j + 1;
        }
        
        if matches {
            proof {
                lemma_subrange_equality(sub, main, i as int, (i + sub.len()) as int);
            }
            return true;
        }
        
        i = i + 1;
    }
    
    false
}
// </vc-code>

fn main() {
}

}