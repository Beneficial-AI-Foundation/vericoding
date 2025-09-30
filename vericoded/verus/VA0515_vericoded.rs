// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_temperature(temp: int) -> bool {
    -40 <= temp <= 40
}

spec fn expected_output(temp: int) -> Seq<char> {
    if temp >= 30 { seq!['Y', 'e', 's', '\n'] } else { seq!['N', 'o', '\n'] }
}

spec fn correct_output(temp: int, output: Seq<char>) -> bool {
    output == expected_output(temp)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): replaced byte literals with numeric u8 and kept proofs establishing expected output */
fn build_output_vec(temp: i8) -> (v: Vec<u8>)
    ensures
        v@.map(|i: int, b: u8| b as char) == expected_output(temp as int),
{
    if temp >= 30 {
        let v1: Vec<u8> = vec![89u8, 101u8, 115u8, 10u8];
        proof {
            assert((89u8 as char) == 'Y');
            assert((101u8 as char) == 'e');
            assert((115u8 as char) == 's');
            assert((10u8 as char) == '\n');
            assert(v1@.map(|i: int, b: u8| b as char) == seq!['Y', 'e', 's', '\n']);
            assert(expected_output(temp as int) == seq!['Y', 'e', 's', '\n']);
        }
        v1
    } else {
        let v2: Vec<u8> = vec![78u8, 111u8, 10u8];
        proof {
            assert((78u8 as char) == 'N');
            assert((111u8 as char) == 'o');
            assert((10u8 as char) == '\n');
            assert(v2@.map(|i: int, b: u8| b as char) == seq!['N', 'o', '\n']);
            assert(expected_output(temp as int) == seq!['N', 'o', '\n']);
        }
        v2
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: Vec<u8>)
    requires valid_temperature(x as int)
    ensures correct_output(x as int, result@.map(|i: int, b: u8| b as char))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): call helper and return vector of bytes for expected output */
    let result = build_output_vec(x);
    result
}
// </vc-code>


}

fn main() {}