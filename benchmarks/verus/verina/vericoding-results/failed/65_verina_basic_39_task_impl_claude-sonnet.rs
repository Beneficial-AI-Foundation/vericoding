// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed safe_mod to spec function to allow use in ensures clause */
spec fn safe_mod(a: int, b: int) -> int
{
    ((a % b) + b) % b
}

proof fn mod_properties(a: int, b: int)
    requires b > 0
    ensures 0 <= safe_mod(a, b) < b,
        safe_mod(a, b) == ((a % b) + b) % b
{
}

proof fn rotation_index_lemma(i: int, n: int, len: int)
    requires len > 0, 0 <= i < len
    ensures 0 <= safe_mod(i - n, len) < len
{
    mod_properties(i - n, len);
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
    /* code modified by LLM (iteration 5): added decreases clause to fix compilation error */
    if l.len() == 0 {
        return Vec::new();
    }
    
    let len = l.len();
    let effective_n = n % len;
    let mut result = Vec::with_capacity(len);
    
    let mut i = 0;
    while i < len
        invariant
            result.len() == i,
            i <= len,
            len == l.len(),
            effective_n == n % len,
            forall|j: int| 0 <= j < i ==> {
                let len_int = len as int;
                let rotated_index = safe_mod(j - effective_n as int, len_int);
                result[j] == l[rotated_index]
            }
        decreases len - i
    {
        proof {
            let len_int = len as int;
            let rotated_index = safe_mod(i as int - effective_n as int, len_int);
            mod_properties(i as int - effective_n as int, len_int);
            rotation_index_lemma(i as int, effective_n as int, len_int);
        }
        
        let source_index = if i >= effective_n {
            i - effective_n
        } else {
            len - effective_n + i
        };
        
        result.push(l[source_index]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}