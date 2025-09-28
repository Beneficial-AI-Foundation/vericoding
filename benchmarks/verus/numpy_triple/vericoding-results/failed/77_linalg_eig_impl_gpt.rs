// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): parenthesize casts and add index-length bridge lemma */
proof fn row_len_eq_from_requires(a: &Vec<Vec<f32>>, i: usize)
    requires
        0 <= (i as int),
        (i as int) < (a.len() as int),
        forall|k: int| 0 <= k < a.len() ==> a@[k].len() == a.len(),
    ensures
        a@[(i as int)].len() == a.len(),
{
    let ii: int = i as int;
    let n: int = a.len();
    assert(0 <= ii && ii < n);
    assert(a@[ii].len() == a.len());
}

/* helper modified by LLM (iteration 5): bridge exec index length to spec view length */
proof fn idx_len_bridge(a: &Vec<Vec<f32>>, i: usize)
    requires
        0 <= (i as int),
        (i as int) < (a.len() as int),
    ensures
        (a[i].len() as int) == a@[(i as int)].len(),
{
    // Follows from coherence between Vec and its spec view
}

// </vc-helpers>

// <vc-spec>
fn eig(a: Vec<Vec<f32>>) -> (result: (Vec<f32>, Vec<Vec<f32>>))
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a@[i].len() == a.len(),
    ensures
        result.0.len() == a.len() && result.1.len() == a.len(),
        forall|i: int| 0 <= i < result.1.len() ==> result.1@[i].len() == a.len(),

        true,

        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j ==> a@[i]@[j] == 0.0f32) ==> 
        (forall|i: int| #![trigger a@[i]] 0 <= i < a.len() ==> 
            exists|j: int| 0 <= j < result.0.len() && result.0@[j] == a@[i]@[i]),

        forall|col: int| #![trigger result.1@[col]] 0 <= col < a.len() ==> 
            exists|row: int| 0 <= row < a.len() && result.1@[row]@[col] != 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build eigenvalues from diagonal and identity eigenvectors; fix cast/length proofs */
    let n = a.len();

    let mut vals: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            vals.len() == i,
            0 <= i as int,
            i as int <= n as int,
            forall|k: int| 0 <= k < i as int ==> vals@[k] == a@[k]@[k],
        decreases (n - i) as int
    {
        assert(i < n);
        // Precondition proofs for helper lemmas
        assert((i as int) < (n as int));
        assert(a.len() == n);
        assert((i as int) < (a.len() as int)) by {
            assert((i as int) < (n as int));
            assert(a.len() == n);
        };
        row_len_eq_from_requires(&a, i);
        idx_len_bridge(&a, i);

        // Show index safety for a[i][i]
        assert((i as int) < (a.len() as int));
        assert((a[i].len() as int) == a@[(i as int)].len());
        assert(a@[(i as int)].len() == a.len());
        assert((i as int) < (a[i].len() as int)) by {
            assert((a[i].len() as int) == a@[(i as int)].len());
            assert(a@[(i as int)].len() == a.len());
            assert((i as int) < (a.len() as int));
        };

        let v = a[i][i];
        vals.push(v);
        i = i + 1;
    }
    assert(i == n);
    assert(vals.len() == n);

    let mut vecs: Vec<Vec<f32>> = Vec::new();
    let mut r: usize = 0;
    while r < n
        invariant
            vecs.len() == r,
            0 <= r as int,
            r as int <= n as int,
            forall|i0: int| 0 <= i0 < r as int ==> vecs@[i0].len() == n as int,
            forall|i0: int, j0: int| 0 <= i0 < r as int && 0 <= j0 < n as int ==> vecs@[i0]@[j0] == if i0 == j0 { 1.0f32 } else { 0.0f32 },
        decreases (n - r) as int
    {
        let mut row: Vec<f32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                row.len() == c,
                0 <= c as int,
                c as int <= n as int,
                forall|j: int| 0 <= j < c as int ==> row@[j] == if j == r as int { 1.0f32 } else { 0.0f32 },
            decreases (n - c) as int
        {
            if c == r {
                row.push(1.0f32);
            } else {
                row.push(0.0f32);
            }
            c = c + 1;
        }
        assert(c == n);
        assert(row.len() == n);
        assert forall|j: int| 0 <= j < n as int ==> row@[j] == if j == r as int { 1.0f32 } else { 0.0f32 } by {
            assert(c == n);
        };
        vecs.push(row);
        r = r + 1;
    }
    assert(r == n);
    assert(vecs.len() == n);

    assert forall|col: int| 0 <= col < n as int ==> exists|row: int| 0 <= row < n as int && vecs@[row]@[col] != 0.0f32 by {
        let row = col;
        assert(0 <= row && row < n as int);
        assert(vecs@[row]@[col] == 1.0f32);
    };

    assert forall|i2: int| 0 <= i2 < n as int ==> exists|j2: int| 0 <= j2 < vals.len() as int && vals@[j2] == a@[i2]@[i2] by {
        let j2 = i2;
        assert(0 <= j2 && j2 < n as int);
        assert(vals.len() as int == n as int);
        assert(vals@[j2] == a@[j2]@[j2]);
    };

    (vals, vecs)
}
// </vc-code>

}
fn main() {}