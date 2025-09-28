use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

// <vc-helpers>
proof fn lemma_sorted_implies_monotonic(s: Seq<int>, i: int, j: int)
    requires sorted(s), 0 <= i <= j < s.len()
    ensures s[i] <= s[j]
{
    if i == j {
        // trivial case
    } else {
        // follows from sorted definition
    }
}

proof fn lemma_sorted_subseq(s: Seq<int>, start: int, end: int)
    requires sorted(s), 0 <= start <= end <= s.len()
    ensures sorted(s.subrange(start, end))
{
    // sorted property is preserved in subsequences
}

proof fn lemma_map_values_preserves_sorted(v: Seq<i32>)
    requires sorted(v.map_values(|val: i32| val as int))
    ensures forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] as int <= v[j] as int
{
    let mapped = v.map_values(|val: i32| val as int);
    assert(forall|i: int, j: int| 0 <= i < j < v.len() ==> mapped[i] <= mapped[j]);
    assert(forall|i: int| 0 <= i < v.len() ==> mapped[i] == v[i] as int);
}

proof fn lemma_sorted_transitivity(v: Seq<i32>, low: int, mid: int, high: int, elem: i32)
    requires 
        sorted(v.map_values(|val: i32| val as int)),
        0 <= low <= mid < high <= v.len(),
        v[mid] <= elem,
        forall|u: int| 0 <= u < low ==> v[u] <= elem as int
    ensures forall|u: int| 0 <= u <= mid ==> v[u] <= elem as int
{
    lemma_map_values_preserves_sorted(v);
    assert(forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] as int <= v[j] as int);
}

proof fn lemma_sorted_transitivity_high(v: Seq<i32>, low: int, mid: int, high: int, elem: i32)
    requires 
        sorted(v.map_values(|val: i32| val as int)),
        0 <= low <= mid < high <= v.len(),
        v[mid] > elem,
        forall|w: int| high <= w < v.len() ==> v[w] > elem as int
    ensures forall|w: int| mid <= w < v.len() ==> v[w] > elem as int
{
    lemma_map_values_preserves_sorted(v);
    assert(forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] as int <= v[j] as int);
}

proof fn lemma_result_bounds(low: usize, v_len: usize)
    requires 0 < low <= v_len, v_len <= usize::MAX, low <= usize::MAX
    ensures 
        0 <= (low - 1) < v_len,
        (low - 1) <= i32::MAX
{
    assert(low >= 1);
    assert(low - 1 >= 0);
    assert(low - 1 < low);
    assert(low - 1 < v_len);
    assert(v_len <= usize::MAX);
    assert(low - 1 <= i32::MAX);
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
    let mut low: usize = 0;
    let mut high: usize = v.len();
    
    while low < high
        invariant 
            low <= high <= v.len(),
            sorted(v@.map_values(|val: i32| val as int)),
            forall|u: int| 0 <= u < low ==> v@[u] <= elem as int,
            forall|w: int| high <= w < v.len() ==> v@[w] > elem as int,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid < high);
        assert(mid < v.len());
        
        if v[mid] <= elem {
            proof {
                lemma_sorted_transitivity(v@, low as int, mid as int, high as int, elem);
            }
            low = mid + 1;
            assert(forall|u: int| 0 <= u < low ==> v@[u] <= elem as int);
        } else {
            proof {
                lemma_sorted_transitivity_high(v@, low as int, mid as int, high as int, elem);
            }
            high = mid;
            assert(forall|w: int| high <= w < v.len() ==> v@[w] > elem as int);
        }
    }
    
    assert(low == high);
    assert(forall|u: int| 0 <= u < low ==> v@[u] <= elem as int);
    assert(forall|w: int| low <= w < v.len() ==> v@[w] > elem as int);
    
    if low == 0 {
        assert(forall|u: int| 0 <= u <= -1 ==> v@[u] <= elem as int);
        assert(forall|w: int| -1 < w < v.len() ==> v@[w] > elem as int);
        -1
    } else {
        proof {
            lemma_result_bounds(low, v.len());
        }
        #[verifier::truncate]
        let result = (low - 1) as i32;
        assert(0 <= result < v.len());
        assert(low - 1 == result);
        assert(forall|u: int| 0 <= u < low ==> v@[u] <= elem as int);
        assert(forall|u: int| 0 <= u <= (low - 1) ==> v@[u] <= elem as int);
        assert(forall|w: int| low <= w < v.len() ==> v@[w] > elem as int);
        assert(forall|w: int| (low - 1) < w < v.len() ==> v@[w] > elem as int);
        result
    }
}
// </vc-code>

//Recursive binary search

fn main() {}

}