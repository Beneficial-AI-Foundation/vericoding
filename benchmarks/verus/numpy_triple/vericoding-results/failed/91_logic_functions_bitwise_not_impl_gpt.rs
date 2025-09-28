// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): arithmetic helper to compute two's-complement bitwise-not for i8 without overflow */
fn not_i8_arith(x: i8) -> (res: i8)
    ensures
        res as int == -(x as int + 1),
{
    if x == i8::MIN {
        let r: i8 = i8::MAX;
        proof {
            assert(r as int == 127);
            assert(x as int == -128);
            assert(r as int == -(x as int + 1));
        }
        r
    } else {
        let neg: i8 = -x;
        let r: i8 = neg - 1i8;
        proof {
            assert(neg as int == -(x as int));
            assert(r as int == neg as int - 1);
            assert(r as int == -(x as int) - 1);
            assert(r as int == -(x as int + 1));
        }
        r
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_bitwise_not(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == -(x[i] as int + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result with loop and prove prefix property using forall without closure requires/ensures */
    let n = x.len();
    let mut result: Vec<i8> = Vec::new();
    let ghost mut s: Seq<i8> = Seq::empty();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            s == result@,
            s.len() as int == i as int,
            forall|j: int| 0 <= j < i as int ==> s[j] as int == -(x@[j] as int + 1),
        decreases (n - i) as int
    {
        let xi = x[i];
        let yi = not_i8_arith(xi);
        let ghost s_old = s;
        result.push(yi);
        proof {
            assert(result@ == s_old.push(yi));
            s = s_old.push(yi);
            assert(s == result@);
            assert(s.len() as int == i as int + 1);
            assert(s[i as int] == yi);
            assert(x@[i as int] == xi);
            assert(yi as int == -(xi as int + 1));
            assert forall|j: int| 0 <= j < s.len() as int ==> s[j] as int == -(x@[j] as int + 1) by {
                if 0 <= j && j < s.len() as int {
                    if j < i as int {
                        assert(s_old.len() as int == i as int);
                        assert(0 <= j && j < s_old.len() as int);
                        assert(s[j] == s_old[j]);
                        assert(s_old[j] as int == -(x@[j] as int + 1));
                    } else {
                        assert(j == i as int);
                        assert(s[j] == yi);
                        assert(yi as int == -(x@[j] as int + 1));
                    }
                }
            };
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}