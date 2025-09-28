// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): ensure cast-multiplication equality used in loop step */
proof fn lemma_mul_cast_i8_int(a: i8, b: i8)
    ensures
        (a * b) as int == (a as int) * (b as int),
{
    assert((a * b) as int == (a as int) * (b as int));
}

/* helper modified by LLM (iteration 2): ensure consistency between i8->i32 cast to int and direct cast */
proof fn lemma_cast_i32_of_i8_to_int(x: i8)
    ensures
        (x as i32) as int == x as int,
{
    assert((x as i32) as int == x as int);
}
// </vc-helpers>

// <vc-spec>
spec fn vec_product_int(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        1
    } else {
        (a[0] as int) * vec_product_int(a.skip(1))
    }
}

fn prod(a: Vec<i8>) -> (result: i8)
    ensures 
        result as int == vec_product_int(a@.map(|i, x| x as i32)),
        a.len() == 0 ==> result == 1,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> result == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed spec indexing by avoiding a[i] in proof and relating x to a@[(i as int)] */
    let mut i: usize = 0;
    let mut acc: i8 = 1;
    while i < a.len()
        invariant
            i <= a.len(),
            (acc as int) * vec_product_int(a@.map(|j, x| x as i32).skip(i as int)) == vec_product_int(a@.map(|j, x| x as i32)),
        decreases a.len() - i
    {
        let x = a[i];
        proof {
            let s = a@.map(|j, x| x as i32);
            let ii = i as int;
            assert(ii < s.len());
            assert(vec_product_int(s.skip(ii)) == (s[ii] as int) * vec_product_int(s.skip(ii + 1)));
            assert(s[ii] == (a@[(ii)] as i32));
            lemma_cast_i32_of_i8_to_int(a@[(ii)]);
            assert((s[ii]) as int == (a@[(ii)] as int));
            assert(x == a@[(ii)]);
            lemma_mul_cast_i8_int(acc, x);
        }
        acc = acc * x;
        i = i + 1;
    }
    acc
}
// </vc-code>


}
fn main() {}