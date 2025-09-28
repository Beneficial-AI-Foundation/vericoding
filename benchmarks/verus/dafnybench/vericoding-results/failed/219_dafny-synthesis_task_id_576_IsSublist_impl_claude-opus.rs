use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to check if sub matches main starting at position start
proof fn sublist_match_implies_subrange(sub: Seq<int>, main: Seq<int>, start: int)
    requires
        0 <= start <= main.len() - sub.len(),
        forall|k: int| 0 <= k < sub.len() ==> sub[k] == main[start + k],
    ensures
        sub =~= main.subrange(start, start + sub.len()),
{
    assert forall|k: int| 0 <= k < sub.len() implies sub[k] == main.subrange(start, start + sub.len())[k] by {
        assert(main.subrange(start, start + sub.len())[k] == main[start + k]);
    }
    assert(sub.len() == main.subrange(start, start + sub.len()).len());
}

proof fn subrange_implies_match(sub: Seq<int>, main: Seq<int>, i: int, j: int)
    requires
        0 <= i <= main.len() - sub.len(),
        j == i + sub.len(),
        sub =~= main.subrange(i, j),
    ensures
        forall|k: int| 0 <= k < sub.len() ==> sub[k] == main[i + k],
{
    assert forall|k: int| 0 <= k < sub.len() implies sub[k] == main[i + k] by {
        assert(sub[k] == main.subrange(i, j)[k]);
        assert(main.subrange(i, j)[k] == main[i + k]);
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
    if sub.len() == 0nat {
        // Empty sequence is always a sublist
        proof {
            assert(sub =~= main.subrange(0, 0));
        }
        return true;
    }
    
    if main.len() < sub.len() {
        // sub is longer than main, cannot be a sublist
        return false;
    }
    
    let mut i: usize = 0;
    while i <= (main.len() - sub.len()) as usize
        invariant
            i <= (main.len() - sub.len() + 1) as usize,
            forall|idx: int| 0 <= idx < i ==> !(sub =~= #[trigger] main.subrange(idx, idx + sub.len() as int)),
    {
        let mut matches = true;
        let mut j: usize = 0;
        
        while j < sub.len() as usize
            invariant
                j <= sub.len() as usize,
                matches == (forall|k: int| 0 <= k < j ==> sub@[k] == main@[i as int + k]),
                i + j <= main.len() as usize,
        {
            if sub@[j as int] != main@[(i + j) as int] {
                matches = false;
                proof {
                    assert(!(forall|k: int| 0 <= k < sub.len() ==> sub@[k] == main@[i as int + k]));
                }
                break;
            }
            j = j + 1;
        }
        
        if matches {
            proof {
                assert(forall|k: int| 0 <= k < sub.len() ==> sub@[k] == main@[i as int + k]);
                sublist_match_implies_subrange(sub, main, i as int);
                assert(sub =~= main.subrange(i as int, i as int + sub.len() as int));
            }
            return true;
        }
        
        proof {
            assert(!(sub =~= main.subrange(i as int, i as int + sub.len() as int))) by {
                if sub =~= main.subrange(i as int, i as int + sub.len() as int) {
                    subrange_implies_match(sub, main, i as int, i as int + sub.len() as int);
                    assert(false);
                }
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(forall|idx: int| 0 <= idx <= main.len() - sub.len() ==> 
               !(sub =~= #[trigger] main.subrange(idx, idx + sub.len() as int)));
    }
    false
}
// </vc-code>

fn main() {
}

}