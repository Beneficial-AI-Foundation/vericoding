use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

// <vc-helpers>
proof fn sorted_implies_ordered(s: Seq<int>, i: int, j: int)
    requires
        sorted(s),
        0 <= i <= j < s.len(),
    ensures
        s[i] <= s[j],
{
    assert(0 <= i < j < s.len() || i == j);
    if i < j {
        assert(sorted(s) ==> s[i] <= s[j]); // by definition of sorted
    }
}

proof fn sorted_subseq(s: Seq<int>, start: int, end: int)
    requires
        sorted(s),
        0 <= start <= end <= s.len(),
    ensures
        sorted(s.subrange(start, end)),
{
    let sub = s.subrange(start, end);
    assert forall|u: int, w: int| 0 <= u < w < sub.len() implies sub[u] <= sub[w] by {
        assert(sub[u] == s[start + u]);
        assert(sub[w] == s[start + w]);
        assert(0 <= start + u < start + w < s.len());
        sorted_implies_ordered(s, start + u, start + w);
    }
}

proof fn mapped_sorted(v: &Vec<i32>)
    requires sorted(v@.map_values(|val: i32| val as int)),
    ensures 
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v@[i] as int <= v@[j] as int,
{
    let s_mapped = v@.map_values(|val: i32| val as int);
    assert forall|i: int, j: int| 0 <= i <= j < v.len() implies v@[i] as int <= v@[j] as int by {
        if 0 <= i <= j < v.len() {
            assert(s_mapped[i] == v@[i] as int);
            assert(s_mapped[j] == v@[j] as int);
            sorted_implies_ordered(s_mapped, i, j);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(v: &Vec<i32>, elem: i32) -> (p: i32)
    requires sorted(v@.map_values(|val: i32| val as int)),
    ensures ({
        &&& -1 <= p < v.len()
        &&& forall|u: int| 0 <= u <= p ==> v@[u] <= elem as int
        &&& forall|w: int| p < w < v.len() ==> v@[w] > elem as int
    }),
// </vc-spec>
// <vc-code>
{
    let mut lo: i32 = 0;
    let mut hi: i32 = if v.len() == 0 { -1 } else { #[verifier::truncate] (v.len() - 1) as i32 };
    
    while lo <= hi
        invariant
            0 <= lo <= #[verifier::truncate] (v.len() as i32),
            -1 <= hi < #[verifier::truncate] (v.len() as i32),
            lo <= hi + 1,
            forall|u: int| 0 <= u < lo ==> #[trigger] v@[u] <= elem as int,
            forall|w: int| hi < w < v.len() ==> #[trigger] v@[w] > elem as int,
        decreases hi - lo,
    {
        let mid: i32 = lo + (hi - lo) / 2;
        
        assert(0 <= lo <= mid <= hi < #[verifier::truncate] (v.len() as i32)) by {
            assert((hi - lo) / 2 >= 0);
            assert((hi - lo) / 2 <= hi - lo);
        }
        
        if v[mid as usize] <= elem {
            assert forall|u: int| 0 <= u <= mid implies #[trigger] v@[u] <= elem as int by {
                assert forall|u: int| 0 <= u < lo implies v@[u] <= elem as int by {}
                assert forall|u: int| lo <= u <= mid implies v@[u] <= elem as int by {
                    if lo <= u <= mid {
                        mapped_sorted(v);
                        assert(v@[u] as int <= v@[mid as int] as int);
                        assert(v@[mid as int] <= elem as int);
                    }
                }
            }
            assert(mid < #[verifier::truncate] (v.len() as i32));
            assert(mid + 1 <= #[verifier::truncate] (v.len() as i32));
            lo = mid + 1;
        } else {
            assert forall|w: int| mid <= w < v.len() implies #[trigger] v@[w] > elem as int by {
                assert forall|w: int| hi < w < v.len() implies v@[w] > elem as int by {}
                assert forall|w: int| mid <= w <= hi implies v@[w] > elem as int by {
                    if mid <= w <= hi {
                        mapped_sorted(v);
                        assert(v@[mid as int] as int <= v@[w] as int);
                        assert(v@[mid as int] > elem as int);
                    }
                }
            }
            hi = mid - 1;
        }
    }
    
    assert(lo == hi + 1);
    assert(forall|u: int| 0 <= u <= hi ==> v@[u] <= elem as int);
    assert(forall|w: int| hi < w < v.len() ==> v@[w] > elem as int);
    
    hi
}
// </vc-code>

//Recursive binary search

fn main() {}

}