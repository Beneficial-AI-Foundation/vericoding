use vstd::prelude::*;

verus! {

fn polyder(poly: &Vec<i32>, m: usize) -> (ret: Vec<i32>)
    requires 
        m > 0,
        poly.len() <= i32::MAX,
        m <= i32::MAX,
    ensures ret.len() == if poly.len() <= m { 0 } else { poly.len() - m }
{
    if poly.len() <= m {
        Vec::new()
    } else {
        let mut ret = Vec::with_capacity(poly.len() - m);
        let mut i = 0usize;
        while i < poly.len() - m
            invariant 
                0 <= i <= poly.len() - m,
                ret.len() == i,
                poly.len() > m,
                i <= i32::MAX,
                m <= i32::MAX,
                poly.len() <= i32::MAX,
            decreases poly.len() - m - i
        {
            let mut coeff = poly[i + m];
            let mut j = 0usize;
            while j < m
                invariant 
                    0 <= j <= m,
                    i + m >= j,
                    i <= i32::MAX,
                    m <= i32::MAX,
                    j <= i32::MAX,
                decreases m - j
            {
                assert(i + m >= j);
                #[verifier::truncate]
                let factor = (i + m - j) as i32;
                coeff = coeff.wrapping_mul(factor);
                j = j + 1;
            }
            ret.push(coeff);
            i = i + 1;
        }
        ret
    }
}

fn main() {}

}