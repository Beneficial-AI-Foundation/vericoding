use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn subtract_sequences(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] - b[i],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<int> = Vec::new();
    let len = a.len();

    // Loop invariant:
    // 1. the length of 'result' is equal to 'i'
    // 2. for all 'j' from 0 up to 'i', result[j] == a[j] - b[j]
    // 3. 'i' is always within the bounds [0, len]
    // 4. 'result' capacity always greater or equal to 'len'
    // 5. 'i' is an integer
    // 6. Vector 'result' is well-formed
    while result.len() < len as usize
        invariant
            0 <= result.len(),
            result.len() <= len as usize,
            result.capacity() >= len as usize,
            forall|j: int| 0 <= j && (j as nat) < result.len() as nat ==> result@[j as nat] == a.view_nth(j as nat) - b.view_nth(j as nat),
    {
        let i_usize = result.len();
        let i: nat = i_usize as nat; // Convert usize to nat here
        let diff = a.view_nth(i) - b.view_nth(i);
        result.push(diff);
    }

    // After the loop, result.len() == len holds.
    // And, forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] - b[i] holds.
    // So, we can convert to a sequence and return.
    result.to_vec().into_iter().collect::<Seq<int>>()
}
// </vc-code>

fn main() {}

}