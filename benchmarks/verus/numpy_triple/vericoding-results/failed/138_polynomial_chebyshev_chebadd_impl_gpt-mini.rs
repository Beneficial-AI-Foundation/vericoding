// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): length cast to int nonnegativity */
fn lemma_vec_len_nonneg<T>(v: &Vec<T>)
    ensures
        (v.len() as int) >= 0,
{
    proof {
        // trivial: casting usize length to int yields non-negative value
        assert(v.len() as int >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn chebadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int + c2[i] as int
            } else if i < c1.len() {
                result[i] == c1[i]
            } else if i < c2.len() {
                result[i] == c2[i]
            } else {
                result[i] == 0
            }
        },
        forall|i: int| 0 <= i < c1.len() ==> c1[i] != 0 ==> {
            exists|j: int| 0 <= j < result.len() && j == i && {
                if i < c2.len() {
                    result[j] as int == c1[i] as int + c2[i] as int
                } else {
                    result[j] == c1[i]
                }
            }
        },
        forall|i: int| 0 <= i < c2.len() ==> c2[i] != 0 ==> {
            exists|j: int| 0 <= j < result.len() && j == i && {
                if i < c1.len() {
                    result[j] as int == c1[i] as int + c2[i] as int
                } else {
                    result[j] == c2[i]
                }
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement chebadd using usize loop and int-indexed invariants */
    let len1: usize = c1.len();
    let len2: usize = c2.len();
    let maxlen: usize = if len1 >= len2 { len1 } else { len2 };
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0usize;
    while i < maxlen
        invariant
            i <= maxlen,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> {
                if k < (len1 as int) && k < (len2 as int) {
                    result[k] as int == c1[k] as int + c2[k] as int
                } else if k < (len1 as int) {
                    result[k] == c1[k]
                } else if k < (len2 as int) {
                    result[k] == c2[k]
                } else {
                    result[k] == 0
                }
            },
        decreases maxlen - i
    {
        if i < len1 && i < len2 {
            let s: int = (c1[i] as int) + (c2[i] as int);
            let v: i8 = s as i8;
            result.push(v);
        } else if i < len1 {
            result.push(c1[i]);
        } else if i < len2 {
            result.push(c2[i]);
        } else {
            result.push(0i8);
        }
        i = i + 1usize;
    }
    result
}
// </vc-code>


}
fn main() {}