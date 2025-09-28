use vstd::prelude::*;

verus! {

// <vc-helpers>
fn create_vec_from_seq<T: Copy>(s: &Seq<T>) -> (v: Vec<T>)
    ensures v.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> v@[i] == s@[i]
{
    let mut v = Vec::new();
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == s@[j]
    {
        v.push(s@[i]);
        i = i + 1;
    }
    v
}

fn create_seq_from_vec<T: Copy>(v: &Vec<T>) -> (s: Seq<T>)
    ensures s.len() == v.len(),
            forall|i: int| 0 <= i < v.len() ==> s@[i] == v@[i]
{
    // Fix: Use v.len() as `usize` for `create_seq_from_vec`
    Seq::new(v.len() as nat, |i: nat| v.tracked_element_at(i as int).unwrap())
}

macro_rules! ghost_dbg {
    ($($arg:tt)*) => {
        #[cfg(feature = "print_ghost_dbg")]
        {
            dbg!($($arg)*);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn index_wise_addition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> (result: Seq<Seq<int>>)
    requires 
        a.len() > 0 && b.len() > 0,
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == b[i].len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == a[i].len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == a[i][j] + b[i][j],
// </vc-spec>
// <vc-code>
{
    let mut result_vec: Vec<Vec<int>> = Vec::new();
    let mut i: int = 0;

    ghost_dbg!(a.len());
    ghost_dbg!(a[0].len());

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result_vec.len() == i,
            forall|k: int| 0 <= k < i ==> {
                && result_vec@[k].len() == a[k].len()
                && forall|l: int| 0 <= l < a[k].len() ==> result_vec@[k]@[l] == a[k][l] + b[k][l]
            },
    {
        let mut inner_vec: Vec<int> = Vec::new();
        let mut j: int = 0;
        
        // Assert property of inner sequence length before inner loop
        assert(a[i].len() == b[i].len());

        while j < a[i].len()
            invariant
                0 <= j <= a[i].len(),
                inner_vec.len() == j,
                forall|k: int| 0 <= k < j ==> inner_vec@[k] == a[i][k] + b[i][k]
        {
            inner_vec.push(a[i][j] + b[i][j]);
            j = j + 1;
        }
        result_vec.push(inner_vec);
        i = i + 1;
    }

    // Fix: Use result_vec.len() and a[k].len() directly, as they return `usize`
    let mut result_seq: Seq<Seq<int>> = Seq::new(result_vec.len() as nat, |k: nat| 
        Seq::new(a[k as int].len() as nat, |l: nat| result_vec.tracked_element_at(k as int).unwrap().tracked_element_at(l as int).unwrap()));

    // Proofs for the ensures clause
    assert(result_seq.len() == a.len());
    assert(forall|k: int| 0 <= k < result_seq.len() ==> result_seq[k].len() == a[k].len());
    assert(forall|k: int, l: int| #[trigger] (0 <= k < result_seq.len() && 0 <= l < result_seq[k].len()) ==> result_seq[k][l] == a[k][l] + b[k][l]);

    result_seq
}
// </vc-code>

fn main() {}

}