// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow check for i8 addition */
fn add_i8_safe(a: i8, b: i8) -> (result: i8)
    requires
        a as int + b as int >= -128,
        a as int + b as int <= 127
    ensures
        result as int == a as int + b as int
{
    a + b
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
    /* code modified by LLM (iteration 5): fixed int literal types */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::with_capacity(max_len);
    let mut i = 0;
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if j < c1.len() && j < c2.len() {
                    result[j] as int == c1[j] as int + c2[j] as int
                } else if j < c1.len() {
                    result[j] == c1[j]
                } else if j < c2.len() {
                    result[j] == c2[j]
                } else {
                    result[j] == 0
                }
            }
        decreases max_len - i
    {
        let val = if i < c1.len() && i < c2.len() {
            let ghost sum: int = c1[i as int] as int + c2[i as int] as int;
            if sum >= -128int && sum <= 127int {
                add_i8_safe(c1[i], c2[i])
            } else {
                if sum > 127int { 127 } else { -128 }
            }
        } else if i < c1.len() {
            c1[i]
        } else if i < c2.len() {
            c2[i]
        } else {
            0
        };
        
        result.push(val);
        
        proof {
            assert(result.len() == i + 1);
            assert(forall|j: int| 0 <= j < i ==> {
                if j < c1.len() && j < c2.len() {
                    result[j] as int == c1[j] as int + c2[j] as int
                } else if j < c1.len() {
                    result[j] == c1[j]
                } else if j < c2.len() {
                    result[j] == c2[j]
                } else {
                    result[j] == 0
                }
            });
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}