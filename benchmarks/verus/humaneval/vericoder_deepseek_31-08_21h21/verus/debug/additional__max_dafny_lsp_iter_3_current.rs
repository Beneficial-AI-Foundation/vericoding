use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_max_index_in_range(a: Seq<i32>, max_index: int)
    requires
        a.len() > 0,
        0 <= max_index < a.len() as int,
        forall|k: int| 0 <= k < a.len() as int ==> a[k] <= a[max_index]
    ensures
        0 <= max_index < a.len() as int
{
}

proof fn lemma_transitive_inequality(x: i32, y: i32, z: i32)
    requires
        x <= y,
        y <= z
    ensures
        x <= z
{
}

spec fn find_max_index(a: Seq<i32>, i: int, j: int, current_max: int) -> (max_index: int)
    recommends i <= j
    requires
        0 <= i <= a.len(),
        0 <= j <= a.len(),
        0 <= current_max < a.len(),
        forall|k: int| 0 <= k < i ==> a[k] <= a[current_max]
    ensures
        0 <= max_index < a.len(),
        forall|k: int| 0 <= k < j ==> a[k] <= a[max_index]
    decreases j - i
{
    if i < j {
        let candidate = if a[i] > a[current_max] { i } else { current_max };
        find_max_index(a, i+1, j, candidate)
    } else {
        current_max
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut index: usize = 0;
    let mut i: usize = 1;
    let n = a.len();
    
    while i < n
        invariant
            0 <= index < n,
            0 <= i <= n,
            forall|k: int| 0 <= k < i ==> a[k] <= a[index as int]
        decreases n - i
    {
        if a[i] > a[index] {
            index = i;
        }
        i = i + 1;
    }
    
    proof {
        lemma_max_index_in_range(a@, index as int);
    }
    
    index
}
// </vc-code>

fn main() {}
}