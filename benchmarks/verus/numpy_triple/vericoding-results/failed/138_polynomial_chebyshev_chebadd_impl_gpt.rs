// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple max on usize */
fn max_usize(a: usize, b: usize) -> (r: usize)
    ensures
        r == if a >= b { a } else { b },
{
    if a >= b { a } else { b }
}

/* helper modified by LLM (iteration 5): simple min on usize */
fn min_usize(a: usize, b: usize) -> (r: usize)
    ensures
        r == if a <= b { a } else { b },
{
    if a <= b { a } else { b }
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
    /* code modified by LLM (iteration 5): implement single loop over max_len with guarded indexing and strong invariant capturing spec */
    let l1 = c1.len();
    let l2 = c2.len();
    let max_len = if l1 >= l2 { l1 } else { l2 };

    let mut res: Vec<i8> = Vec::new();

    let mut i: usize = 0;
    while i < max_len
        invariant
            i <= max_len,
            res.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> {
                if j < l1 as int && j < l2 as int {
                    res@[j] as int == c1@[j] as int + c2@[j] as int
                } else if j < l1 as int {
                    res@[j] == c1@[j]
                } else if j < l2 as int {
                    res@[j] == c2@[j]
                } else {
                    res@[j] == 0
                }
            },
        decreases max_len - i
    {
        let v: i8;
        if i < l1 && i < l2 {
            v = c1[i] + c2[i];
        } else if i < l1 {
            v = c1[i];
        } else if i < l2 {
            v = c2[i];
        } else {
            v = 0;
        }
        res.push(v);
        i += 1;
    }

    assert(res.len() == max_len);

    let result = res;

    assert(forall|i: int| 0 <= i && i < result.len() as int ==> {
        if i < l1 as int && i < l2 as int {
            result[i] as int == c1[i] as int + c2[i] as int
        } else if i < l1 as int {
            result[i] == c1[i]
        } else if i < l2 as int {
            result[i] == c2[i]
        } else {
            result[i] == 0
        }
    });

    result
}
// </vc-code>


}
fn main() {}