// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper to check palindrome on vectors */
fn is_palindrome_vec(x: &Vec<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> x[i] == x[x.len() - 1 - i]),
{
    let mut i: usize = 0;
    let n = x.len();
    let mut result = true;
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            n == x.len(),
            result <==> (forall|j: int| 0 <= j < i ==> x[j] == x[n - 1 - j])
    {
        if x[i] != x[n - 1 - i] {
            result = false;
            proof {
                assert(!(forall|j: int| 0 <= j < i + 1 ==> x[j] == x[n - 1 - j])) by {
                    assert(i < i + 1);
                    assert(x[i as int] != x[(n - 1 - i) as int]);
                }
            }
            break;
        }
        i = i + 1;
    }
    
    if result {
        proof {
            assert forall|k: int| 0 <= k < n implies x[k] == x[n - 1 - k] by {
                if k < n / 2 {
                    assert(x[k] == x[n - 1 - k]);
                } else {
                    let k_mirror = n - 1 - k;
                    assert(0 <= k_mirror < n / 2);
                    assert(x[k_mirror] == x[n - 1 - k_mirror]);
                    assert(n - 1 - k_mirror == k);
                }
            }
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed index access - use usize for Vec indexing */
{
    let mut vec_x: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            vec_x.len() == i,
            forall|j: int| 0 <= j < i ==> vec_x[j] == x[j]
    {
        vec_x.push(x[i]);
        i = i + 1;
    }
    
    let result = is_palindrome_vec(&vec_x);
    
    proof {
        assert(vec_x.len() == x.len());
        assert forall|k: int| 0 <= k < x.len() implies vec_x[k] == x[k] by {
            assert(vec_x[k] == x[k]);
        }
        assert(result <==> (forall|m: int| 0 <= m < vec_x.len() ==> vec_x[m] == vec_x[vec_x.len() - 1 - m]));
        assert(result <==> (forall|m: int| 0 <= m < x.len() ==> x[m] == x[x.len() - 1 - m]));
    }
    
    result
}
// </vc-code>

}
fn main() {}