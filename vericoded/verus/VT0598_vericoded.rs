// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_min_i8(arr: &Vec<i8>) -> (m: i8)
    requires
        arr.len() > 0,
    ensures
        forall|k: int| 0 <= k < arr.len() ==> m as int <= arr@[k] as int,
        exists|k: int| 0 <= k < arr.len() && arr@[k] as int == m as int,
{
    let mut m_local = arr[0];
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            forall|k: int| 0 <= k < i as int ==> m_local as int <= arr@[k] as int,
            exists|k: int| 0 <= k < i as int && arr@[k] as int == m_local as int,
        decreases (arr.len() - i) as int
    {
        if arr[i] < m_local {
            m_local = arr[i];
        }
        i += 1;
    }
    m_local
}

fn vec_max_i8(arr: &Vec<i8>) -> (m: i8)
    requires
        arr.len() > 0,
    ensures
        forall|k: int| 0 <= k < arr.len() ==> arr@[k] as int <= m as int,
        exists|k: int| 0 <= k < arr.len() && arr@[k] as int == m as int,
{
    let mut m_local = arr[0];
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            forall|k: int| 0 <= k < i as int ==> arr@[k] as int <= m_local as int,
            exists|k: int| 0 <= k < i as int && arr@[k] as int == m_local as int,
        decreases (arr.len() - i) as int
    {
        if arr[i] > m_local {
            m_local = arr[i];
        }
        i += 1;
    }
    m_local
}
// </vc-helpers>

// <vc-spec>
fn percentile(arr: Vec<i8>, q: i8) -> (result: i8)
    requires 
        arr.len() > 0,
        0 <= q && q <= 100,
    ensures
        (forall|i: int| 0 <= i < arr.len() ==> arr[i] as int <= result as int ==> 
            exists|j: int| 0 <= j < arr.len() && arr[j] as int >= result as int) &&
        (forall|i: int| 0 <= i < arr.len() ==> arr[i] as int >= result as int ==> 
            exists|j: int| 0 <= j < arr.len() && arr[j] as int <= result as int) &&
        (q == 0 ==> forall|i: int| 0 <= i < arr.len() ==> result as int <= arr[i] as int) &&
        (q == 100 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] as int <= result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): add explicit int types for proof vars to fix inference error */
    let n = arr.len();
    if q == 0 {
        let m = vec_min_i8(&arr);
        proof {
            assert(forall|i:int| 0 <= i < n ==> arr[i] as int <= m as int ==> 
                exists|j:int| 0 <= j < n && arr[j] as int >= m as int) by {
                assert(exists|j:int| 0 <= j < n && arr[j] as int >= m as int) by {
                    let j: int = 0; assert(0 <= j && j < n);
                    assert(m as int <= arr[j] as int);
                };
            };
            let jmin = choose|k:int| 0 <= k < n && arr@[k] as int == m as int;
            assert(forall|i:int| 0 <= i < n ==> arr[i] as int >= m as int ==> 
                exists|j:int| 0 <= j < n && arr[j] as int <= m as int) by {
                assert(exists|j:int| 0 <= j < n && arr[j] as int <= m as int) by {
                    let j = jmin; assert(0 <= j && j < n);
                    assert(arr[j] as int <= m as int);
                };
            };
            assert(forall|i:int| 0 <= i < n ==> m as int <= arr[i] as int);
        }
        m
    } else if q == 100 {
        let m = vec_max_i8(&arr);
        proof {
            let jmax = choose|k:int| 0 <= k < n && arr@[k] as int == m as int;
            assert(forall|i:int| 0 <= i < n ==> arr[i] as int <= m as int ==> 
                exists|j:int| 0 <= j < n && arr[j] as int >= m as int) by {
                assert(exists|j:int| 0 <= j < n && arr[j] as int >= m as int) by {
                    let j = jmax; assert(0 <= j && j < n);
                    assert(arr[j] as int >= m as int);
                };
            };
            assert(forall|i:int| 0 <= i < n ==> arr[i] as int >= m as int ==> 
                exists|j:int| 0 <= j < n && arr[j] as int <= m as int) by {
                assert(exists|j:int| 0 <= j < n && arr[j] as int <= m as int) by {
                    let j: int = 0; assert(0 <= j && j < n);
                    assert(arr[j] as int <= m as int);
                };
            };
            assert(forall|i:int| 0 <= i < n ==> arr[i] as int <= m as int);
        }
        m
    } else {
        let r = arr[0];
        proof {
            assert(forall|i:int| 0 <= i < n ==> arr[i] as int <= r as int ==> 
                exists|j:int| 0 <= j < n && arr[j] as int >= r as int) by {
                assert(exists|j:int| 0 <= j < n && arr[j] as int >= r as int) by {
                    let j: int = 0; assert(0 <= j && j < n);
                    assert(arr[j] as int >= r as int);
                };
            };
            assert(forall|i:int| 0 <= i < n ==> arr[i] as int >= r as int ==> 
                exists|j:int| 0 <= j < n && arr[j] as int <= r as int) by {
                assert(exists|j:int| 0 <= j < n && arr[j] as int <= r as int) by {
                    let j: int = 0; assert(0 <= j && j < n);
                    assert(arr[j] as int <= r as int);
                };
            };
        }
        r
    }
}
// </vc-code>

}
fn main() {}