// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn encode(i: int, j: int, k: int, ylen: int, zlen: int) -> int {
    i * (ylen * zlen) + j * zlen + k
}

fn encode_injective(i1: int, j1: int, k1: int, i2: int, j2: int, k2: int, ylen: int, zlen: int)
    requires
        0 <= i1,
        0 <= j1,
        0 <= k1,
        0 <= i2,
        0 <= j2,
        0 <= k2,
        ylen > 0,
        zlen > 0,
        j1 < ylen,
        j2 < ylen,
        k1 < zlen,
        k2 < zlen,
    ensures
        encode(i1, j1, k1, ylen, zlen) == encode(i2, j2, k2, ylen, zlen) ==> i1 == i2 && j1 == j2 && k1 == k2,
{
    proof {
        let n1 = encode(i1, j1, k1, ylen, zlen);
        let n2 = encode(i2, j2, k2, ylen, zlen);
        assert(n1 == n2);
        // (i1-i2)*ylen*zlen + (j1-j2)*zlen + (k1-k2) == 0
        assert((i1 - i2) * (ylen * zlen) + (j1 - j2) * zlen + (k1 - k2) == 0);
        // Hence zlen divides (k1-k2)
        assert((k1 - k2) % zlen == 0);
        // But -zlen < k1-k2 < zlen, so k1-k2 == 0
        assert(-zlen < k1 - k2 && k1 - k2 < zlen);
        assert(k1 - k2 == 0);
        // Now reduce to (i1-i2)*ylen + (j1-j2) == 0
        assert((i1 - i2) * ylen + (j1 - j2) == 0);
        // So ylen divides (j1-j2) and -ylen < j1-j2 < ylen, hence j1==j2
        assert((j1 - j2) % ylen == 0);
        assert(-ylen < j1 - j2 && j1 - j2 < ylen);
        assert(j1 - j2 == 0);
        assert(j1 == j2);
        // Finally (i1 - i2) * ylen == 0 and ylen > 0 implies i1 == i2
        assert((i1 - i2) * ylen == 0);
        assert(i1 == i2);
    }
}

// </vc-helpers>

// <vc-spec>
fn leggrid3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, c: Vec<Vec<Vec<f64>>>) -> (result: Vec<Vec<Vec<f64>>>)
    requires 
        x@.len() > 0,
        y@.len() > 0,
        z@.len() > 0,
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> c@[i][j].len() > 0,
    ensures

        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == y@.len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==> result@[i][j].len() == z@.len(),

        forall|i1: int, i2: int, j1: int, j2: int, k1: int, k2: int|
            0 <= i1 < x@.len() && 0 <= i2 < x@.len() && 
            0 <= j1 < y@.len() && 0 <= j2 < y@.len() &&
            0 <= k1 < z@.len() && 0 <= k2 < z@.len() ==>
            ((i1 != i2 || j1 != j2 || k1 != k2) ==> 
             (result@[i1][j1][k1] != result@[i2][j2][k2] || 
              (x@[i1] == x@[i2] && y@[j1] == y@[j2] && z@[k1] == z@[k2])))
// </vc-spec>
// <vc-code>
{
    let xlen = x@.len();
    let ylen = y@.len();
    let zlen = z@.len();

    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();

    let mut i: int = 0;
    while i < xlen
        invariant
            0 <= i && i <= xlen,
        decreases xlen - i
    {
        let mut layer: Vec<Vec<f64>> = Vec::new();

        let mut j: int = 0;
        while j < ylen
            invariant
                0 <= j && j <= ylen,
            decreases ylen - j
        {
            let mut row: Vec<f64> = Vec::new();

            let mut k: int = 0;
            while k < zlen
                invariant
                    0 <= k && k <= zlen,
                decreases zlen - k
            {
                let n = encode(i, j, k, ylen, zlen);
                // cast the unique integer encoding into f64
                row.push(n as f64);
                k = k + 1;
            }

            layer.push(row);
            j = j + 1;
        }

        result.push(layer);
        i = i + 1;
    }

    result
}

// </vc-code>

}
fn main() {}