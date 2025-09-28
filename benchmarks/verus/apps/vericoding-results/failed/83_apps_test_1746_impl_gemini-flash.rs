// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn has_children(node: int, parents: Seq<int>, n: int) -> bool
    recommends 0 <= node < n, n >= 3, parents.len() == n - 1
{
    exists|i: int| 0 <= i < n - 1 && parents[i] - 1 == node
}

spec fn count_leaf_children(node: int, parents: Seq<int>, n: int) -> int
    recommends 0 <= node < n, n >= 3, parents.len() == n - 1
{
    (Set::new(|i: int| 0 <= i < n - 1 && parents[i] - 1 == node && !has_children(i + 1, parents, n))).len() as int
}

spec fn valid_input(n: int, parents: Seq<int>) -> bool
{
    n >= 3 && parents.len() == n - 1 && 
    (forall|i: int| 0 <= i < n - 1 ==> #[trigger] parents[i] >= 1 && parents[i] <= i + 1)
}

spec fn is_spruce(n: int, parents: Seq<int>) -> bool
    recommends valid_input(n, parents)
{
    forall|node: int| 0 <= node < n && has_children(node, parents, n) ==> 
        count_leaf_children(node, parents, n) >= 3
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_map_values_len<A, B>(s: Seq<A>, f: impl Fn(A) -> B) {
    s.map_values(f).len() == s.len();
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, parents: Vec<i8>) -> (result: String)
    requires 
        valid_input(n as int, parents@.map_values(|x: i8| x as int)),
    ensures 
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
        result@ == seq!['Y', 'e', 's'] <==> is_spruce(n as int, parents@.map_values(|x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    let n_int = n as int;
    let parents_int_seq = parents@.map_values(|x: i8| x as int);

    let mut i: int = 0;
    let mut is_spruce_local: bool = true;

    while i < n_int
        invariant
            0 <= i <= n_int,
            is_spruce_local == (forall|j: int| 0 <= j < i && has_children(j, parents_int_seq, n_int) ==> count_leaf_children(j, parents_int_seq, n_int) >= 3),
            parents_int_seq.len() == n_int - 1,
            n_int >= 3,
            (forall|k: int| 0 <= k < n_int - 1 ==> parents_int_seq[k] >= 1 && parents_int_seq[k] <= k + 1)
        decreases n_int - i
    {
        if has_children(i, parents_int_seq, n_int) {
            if count_leaf_children(i, parents_int_seq, n_int) < 3 {
                is_spruce_local = false;
                break;
            }
        }
        i = i + 1;
    }

    if is_spruce_local {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}