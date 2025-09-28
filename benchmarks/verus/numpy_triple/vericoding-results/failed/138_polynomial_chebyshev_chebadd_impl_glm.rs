// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): Fix invariant structure and handle overflow with i16 casting */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i <= max_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if j < c1.len() {
                    if j < c2.len() {
                        result@[j] as int == c1@[j] as int + c2@[j] as int
                    } else {
                        result@[j] == c1@[j]
                    }
                } else {
                    result@[j] == c2@[j]
                }
            }
        decreases max_len - i
    {
        if i < c1.len() && i < c2.len() {
            let sum = c1[i] as i16 + c2[i] as i16;
            assert(-128 <= sum && sum <= 127);
            result.push(sum as i8);
        } else if i < c1.len() {
            result.push(c1[i]);
        } else {
            assert(i < c2.len());
            result.push(c2[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}