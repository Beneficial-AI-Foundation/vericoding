// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma ensures clause syntax */
proof fn lemma_mod_equivalence(a: int, b: int, m: int)
    requires m > 0
    ensures (a % m) == (b % m) <==> (a - b) % m == 0
{
}

proof fn lemma_rotate_index(i: int, n: int, len: int)
    requires 0 <= i < len, len > 0, 0 <= n < len
    ensures
        (i - n + len) % len == (if i >= n { i - n } else { len - n + i })
{
    if i >= n {
        assert((i - n + len) % len == i - n);
    } else {
        assert((i - n + len) % len == len - n + i);
    }
}
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: &Vec<i32>, n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> {
            let len = l.len() as int;
            let rotated_index = ((i - n as int + len) % len) as int;
            #[trigger] result[i] == l[rotated_index]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed function body structure */
    if l.len() == 0 {
        return Vec::new();
    }
    
    let len = l.len();
    let n_mod = n % len;
    let mut result = Vec::with_capacity(len);
    
    let mut i = 0;
    while i < len
        invariant
            result.len() == i,
            i <= len,
            len == l.len(),
            n_mod < len,
            forall|j: int| 0 <= j < i ==> {
                let expected_index = (j - n_mod as int + len as int) % len as int;
                let actual_index = if j >= n_mod as int { j - n_mod as int } else { len as int - n_mod as int + j };
                actual_index == expected_index && #[trigger] result[j] == l[actual_index]
            },
        decreases len - i
    {
        let rotated_index = if i >= n_mod {
            i - n_mod
        } else {
            len - n_mod + i
        };
        
        proof {
            lemma_rotate_index(i as int, n_mod as int, len as int);
        }
        
        result.push(l[rotated_index]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}