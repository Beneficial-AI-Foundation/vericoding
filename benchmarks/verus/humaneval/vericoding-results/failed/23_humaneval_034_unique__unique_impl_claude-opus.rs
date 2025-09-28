// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_before(s: Seq<i8>, x: i8, end: int) -> bool
    recommends 0 <= end <= s.len()
{
    exists|i: int| 0 <= i < end && s[i] == x
}

proof fn lemma_contains_before_extend(s: Seq<i8>, x: i8, end: int)
    requires
        0 <= end < s.len(),
        contains_before(s, x, end),
    ensures
        contains_before(s, x, end + 1),
{
    let i = choose|i: int| 0 <= i < end && s[i] == x;
    assert(0 <= i < end + 1 && s[i] == x);
}

proof fn lemma_sorted_unique_contains(result: Seq<i8>, s: Seq<i8>)
    requires
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| 0 <= i < result.len() ==> s.contains(result[i]),
    ensures
        forall|x: i8| result.contains(x) ==> s.contains(x),
{
    assert forall|x: i8| result.contains(x) implies s.contains(x) by {
        if result.contains(x) {
            let idx = choose|i: int| 0 <= i < result.len() && result[i] == x;
            assert(s.contains(result[idx]));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i8>) -> (result: Vec<i8>)
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> (result@[i] as int) < (result@[j] as int) &&
        forall|x: i8| result@.contains(x) ==> s@.contains(x) &&
        forall|x: i8| s@.contains(x) ==> result@.contains(x)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int, k: int| 0 <= j < k < result@.len() ==> (result@[j] as int) < (result@[k] as int),
            forall|x: i8| result@.contains(x) ==> s@.contains(x),
            forall|x: i8| contains_before(s@, x, i as int) ==> result@.contains(x),
    {
        let current = s[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                forall|k: int, l: int| 0 <= k < l < result@.len() ==> (result@[k] as int) < (result@[l] as int),
                forall|x: i8| result@.contains(x) ==> s@.contains(x),
                forall|x: i8| contains_before(s@, x, i as int) ==> result@.contains(x),
                !found ==> forall|k: int| 0 <= k < j ==> result@[k] != current,
        {
            if result[j] == current {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if !found {
            let mut insert_pos = 0;
            let mut k = 0;
            
            while k < result.len()
                invariant
                    0 <= k <= result.len(),
                    0 <= insert_pos <= k,
                    forall|l: int| 0 <= l < insert_pos ==> (result@[l] as int) < (current as int),
                    forall|l: int, m: int| 0 <= l < m < result@.len() ==> (result@[l] as int) < (result@[m] as int),
            {
                if result[k] < current {
                    insert_pos = k + 1;
                }
                k = k + 1;
            }
            
            result.insert(insert_pos, current);
            
            proof {
                assert(s@.contains(current));
                assert forall|x: i8| contains_before(s@, x, i as int) implies result@.contains(x) by {
                    if contains_before(s@, x, i as int) {
                        let idx = choose|m: int| 0 <= m < i && s@[m] == x;
                        assert(contains_before(s@, x, i as int));
                    }
                }
            }
        }
        
        proof {
            if i + 1 <= s.len() {
                assert forall|x: i8| contains_before(s@, x, (i + 1) as int) implies result@.contains(x) by {
                    if contains_before(s@, x, (i + 1) as int) {
                        let idx = choose|m: int| 0 <= m < i + 1 && s@[m] == x;
                        if idx == i {
                            assert(s@[i] == x);
                            assert(current == x);
                            assert(result@.contains(x));
                        } else {
                            assert(idx < i);
                            assert(contains_before(s@, x, i as int));
                        }
                    }
                }
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert forall|x: i8| s@.contains(x) implies result@.contains(x) by {
            if s@.contains(x) {
                let idx = choose|j: int| 0 <= j < s@.len() && s@[j] == x;
                assert(contains_before(s@, x, s@.len() as int));
            }
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}