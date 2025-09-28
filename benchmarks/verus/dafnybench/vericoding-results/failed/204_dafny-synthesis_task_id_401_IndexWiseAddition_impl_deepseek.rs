use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_len_nonnegative(x: Seq<Seq<int>>, i: int)
    requires
        0 <= i < x.len(),
    ensures
        x[i].len() >= 0,
{
}

proof fn lemma_vectors_add_index_wise(a: Seq<Seq<int>>, b: Seq<Seq<int>>, result: Seq<Seq<int>>, i: int, j: int)
    requires
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k].len() == b[k].len(),
        result.len() == a.len(),
        forall|k: int| 0 <= k < result.len() ==> result[k].len() == a[k].len(),
        forall|k: int, l: int| 0 <= k < result.len() && 0 <= l < result[k].len() ==> result[k][l] == a[k][l] + b[k][l],
        0 <= i < result.len(),
        0 <= j < result[i].len(),
    ensures
        result[i][j] == a[i][j] + b[i][j],
{
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
    let mut result = Seq::<Seq<int>>::empty();
    let mut i: int = 0;
    while i < a.len() as int
        invariant
            0 <= i <= a.len() as int,
            result.len() == i as nat,
            forall|k: int| 0 <= k < i ==> result[k as nat].len() == a[k as nat].len(),
            forall|k: int, l: int| 0 <= k < i && 0 <= l < result[k as nat].len() ==> result[k as nat][l] == a[k as nat][l] + b[k as nat][l],
    {
        let mut inner_vec = Seq::<int>::empty();
        let mut j: int = 0;
        proof { lemma_len_nonnegative(a, i as int); }
        while j < a[i as nat].len() as int
            invariant
                0 <= j <= a[i as nat].len() as int,
                inner_vec.len() == j as nat,
                forall|l: int| 0 <= l < j ==> inner_vec[l as nat] == a[i as nat][l as nat] + b[i as nat][l as nat],
        {
            inner_vec = inner_vec.push(a[i as nat][j as nat] + b[i as nat][j as nat]);
            j = j + 1;
        }
        result = result.push(inner_vec);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}