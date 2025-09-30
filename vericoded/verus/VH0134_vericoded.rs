// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_nested(s: Vec<i8>) -> (res: bool)
    ensures res == exists|x: int, y: int, z: int, w: int| 0 <= x < y < z < w < s@.len() && s@[x] == 0 && s@[y] == 0 && s@[z] == 1 && s@[w] == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed bounds checking and invariants */
    let n = s.len();
    if n < 4 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < n - 3
        invariant
            0 <= i <= n - 3,
            n == s.len(),
            n >= 4,
            forall|x: int, y: int, z: int, w: int| 
                0 <= x < y < z < w < s@.len() && x < i ==> 
                !(s@[x] == 0 && s@[y] == 0 && s@[z] == 1 && s@[w] == 1),
        decreases n - 3 - i
    {
        if s[i] == 0 {
            let mut j: usize = i + 1;
            while j < n - 2
                invariant
                    0 <= i < n - 3,
                    i < j <= n - 2,
                    n == s.len(),
                    n >= 4,
                    s@[i as int] == 0,
                    forall|y: int, z: int, w: int|
                        i < y < j && y < z < w < s@.len() ==>
                        !(s@[y] == 0 && s@[z] == 1 && s@[w] == 1),
                decreases n - 2 - j
            {
                if s[j] == 0 {
                    let mut k: usize = j + 1;
                    while k < n - 1
                        invariant
                            0 <= i < n - 3,
                            i < j < n - 2,
                            j < k <= n - 1,
                            n == s.len(),
                            n >= 4,
                            s@[i as int] == 0,
                            s@[j as int] == 0,
                            forall|z: int, w: int|
                                j < z < k && z < w < s@.len() ==>
                                !(s@[z] == 1 && s@[w] == 1),
                        decreases n - 1 - k
                    {
                        if s[k] == 1 {
                            let mut l: usize = k + 1;
                            while l < n
                                invariant
                                    0 <= i < n - 3,
                                    i < j < n - 2,
                                    j < k < n - 1,
                                    k < l <= n,
                                    n == s.len(),
                                    n >= 4,
                                    s@[i as int] == 0,
                                    s@[j as int] == 0,
                                    s@[k as int] == 1,
                                    forall|w: int|
                                        k < w < l ==>
                                        s@[w] != 1,
                                decreases n - l
                            {
                                if s[l] == 1 {
                                    assert(0 <= i as int);
                                    assert(i < j as int);
                                    assert(j < k as int);
                                    assert(k < l as int);
                                    assert(l < s@.len());
                                    assert(s@[i as int] == 0);
                                    assert(s@[j as int] == 0);
                                    assert(s@[k as int] == 1);
                                    assert(s@[l as int] == 1);
                                    return true;
                                }
                                l = l + 1;
                            }
                        }
                        k = k + 1;
                    }
                }
                j = j + 1;
            }
        }
        i = i + 1;
    }
    false
}
// </vc-code>


}

fn main() {}