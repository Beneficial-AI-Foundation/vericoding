use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to add two sequences element-wise
spec fn add_sequences(a: Seq<int>, b: Seq<int>) -> Seq<int>
    recommends a.len() == b.len()
{
    Seq::new(a.len(), |j: int| a[j] + b[j])
}

// Lemma to prove properties about add_sequences
proof fn add_sequences_ensures(a: Seq<int>, b: Seq<int>)
    requires a.len() == b.len()
    ensures 
        add_sequences(a, b).len() == a.len(),
        forall|j: int| 0 <= j < a.len() ==> #[trigger] add_sequences(a, b)[j] == a[j] + b[j]
{
    let result = add_sequences(a, b);
    assert forall|j: int| 0 <= j < a.len() implies result[j] == a[j] + b[j] by {
        assert(result[j] == a[j] + b[j]);
    }
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
    let ghost n = a.len();
    
    // Build the result sequence using spec functions
    let result = Seq::new(n, |i: int| {
        let ghost row_a = a[i];
        let ghost row_b = b[i];
        add_sequences(row_a, row_b)
    });
    
    // Prove the postconditions
    assert(result.len() == a.len());
    
    assert forall|i: int| 0 <= i < result.len() implies result[i].len() == a[i].len() by {
        let ghost row_a = a[i];
        let ghost row_b = b[i];
        add_sequences_ensures(row_a, row_b);
        assert(result[i].len() == row_a.len());
        assert(row_a.len() == a[i].len());
    }
    
    assert forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() implies 
        result[i][j] == a[i][j] + b[i][j] by {
        let ghost row_a = a[i];
        let ghost row_b = b[i];
        add_sequences_ensures(row_a, row_b);
        assert(result[i] == add_sequences(row_a, row_b));
        assert(result[i][j] == row_a[j] + row_b[j]);
        assert(result[i][j] == a[i][j] + b[i][j]);
    }
    
    result
}
// </vc-code>

fn main() {}

}