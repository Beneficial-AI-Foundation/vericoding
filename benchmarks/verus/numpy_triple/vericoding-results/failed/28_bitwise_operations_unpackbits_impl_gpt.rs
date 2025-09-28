// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_unpackbits(a: Vec<u8>) -> (result: Vec<u8>)
    requires forall|i: int| 0 <= i < a@.len() ==> a@[i] < 256,
    ensures 
        result@.len() == a@.len() * 8,
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < 8 ==> 
            #[trigger] result@[i * 8 + j] == ((a@[i] as int) / pow(2, (7 - j) as nat)) % 2
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            out@.len() == (i as int) * 8,
            forall|ii: int, jj: int|
                0 <= ii < i as int && 0 <= jj < 8 ==>
                    #[trigger] out@[(ii * 8 + jj) as int] == ((a@[ii] as int) / pow(2, (7 - jj) as nat)) % 2,
        decreases n as int - i as int
    {
        let byte = a[i];
        assert((byte as int) == (a@[(i as int)] as int));
        let mut j: usize = 0;
        while j < 8
            invariant
                0 <= j as int <= 8,
                out@.len() == (i as int) * 8 + j as int,
                forall|jj: int|
                    0 <= jj < j as int ==>
                        #[trigger] out@[(i as int) * 8 + jj] == ((a@[(i as int)] as int) / pow(2, (7 - jj) as nat)) % 2,
                forall|ii: int, jj: int|
                    0 <= ii < i as int && 0 <= jj < 8 ==>
                        #[trigger] out@[(ii * 8 + jj) as int] == ((a@[ii] as int) / pow(2, (7 - jj) as nat)) % 2,
            decreases 8 - j as int
        {
            let two = pow(2, (7 - j as int) as nat);
            let rem = ((byte as int) / two) % 2;
            assert(0 <= rem && rem < 256);
            let bit: u8 = rem as u8;
            out.push(bit);
            assert(out@[(i as int) * 8 + j as int] == bit);
            assert(bit == rem);
            assert(rem == ((a@[(i as int)] as int) / pow(2, (7 - j as int) as nat)) % 2);
            j += 1;
        }
        i += 1;
    }
    assert(out@.len() == a@.len() * 8);
    out
}
// </vc-code>

}
fn main() {}