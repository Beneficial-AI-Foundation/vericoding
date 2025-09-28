// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix vec_sub_at_index to use ghost code for int operations */
fn zero_vec(len: usize) -> (v: Vec<i8>)
    ensures
        v.len() == len,
        forall|i: int| 0 <= i < len ==> v[i] == 0
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == 0
        decreases len - i
    {
        v.push(0);
        i = i + 1;
    }
    v
}

fn vec_sub_at_index(v1: &Vec<i8>, v2: &Vec<i8>, i: usize) -> (diff: i8)
    requires
        i < v1.len(),
        i < v2.len()
    ensures
        diff as int == v1[i] as int - v2[i] as int
{
    ghost {
        let a = v1[i] as int;
        let b = v2[i] as int;
        (a - b) as i8
    }
}
// </vc-helpers>

// <vc-spec>
fn polysub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int - c2[i] as int
            } else if i < c1.len() && i >= c2.len() {
                result[i] == c1[i]
            } else if i >= c1.len() && i < c2.len() {
                result[i] as int == 0 - c2[i] as int
            } else {
                result[i] == 0
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type conversion issues by using ghost blocks for int operations */
    let len1 = c1.len();
    let len2 = c2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };
    
    let mut result = zero_vec(max_len);
    let mut i: usize = 0;
    
    while i < max_len
        invariant
            i <= max_len,
            result.len() == max_len,
            forall|j: int| 0 <= j < i ==> {
                if j < len1 && j < len2 {
                    result[j] as int == c1[j] as int - c2[j] as int
                } else if j < len1 && j >= len2 {
                    result[j] == c1[j]
                } else if j >= len1 && j < len2 {
                    result[j] as int == 0 - (c2[j] as int)
                } else {
                    result[j] == 0
                }
            }
        decreases max_len - i
    {
        if i < len1 && i < len2 {
            result[i] = vec_sub_at_index(&c1, &c2, i);
        } else if i < len1 && i >= len2 {
            result[i] = c1[i];
        } else if i >= len1 && i < len2 {
            proof {
                let diff = 0 - (c2[i] as int);
                result[i] = diff as i8;
            }
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}