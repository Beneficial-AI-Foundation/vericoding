// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn mod_index(i: int, n: nat) -> nat { if n == 0 { 0 } else { (i % (n as int)) as nat } }
proof fn lemma_mod_range(i: int, n: nat)
    ensures
        n > 0 ==> 0 <= (i % (n as int)) < (n as int)
{ }
// </vc-helpers>

// <vc-spec>
fn resize<T>(a: Vec<T>, new_size: usize) -> (result: Vec<T>)
    ensures
        result.len() == new_size,
        forall|i: int| 0 <= i < new_size ==> {
            if i < a.len() {
                result[i] == a[i]
            } else if a.len() > 0 {
                result[i] == a[(i % a.len() as int) as int]
            } else {
                true
            }
        }
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    if new_size <= len {
        let mut tmp = a;
        tmp.truncate(new_size);
        tmp
    } else if len == 0 {
        Vec::new()
    } else {
        let mut result: Vec<T> = Vec::new();
        result.reserve_exact(new_size);
        let mut i: usize = 0;
        while i < new_size
            invariant
                result.len() == i,
                i <= new_size,
                len == a.len(),
                0 < len,
                forall|k: int| 0 <= k < i as int ==> {
                    if k < len as int {
                        result[k] == a[k]
                    } else {
                        result[k] == a[(k % (len as int)) as int]
                    }
                }
            decreases (new_size - i) as int
        {
            let idx = if i < len { i } else { i % len };
            let x = a[idx].clone();
            result.push(x);
            i = i + 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}