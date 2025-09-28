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
/* helper modified by LLM (iteration 5): convert runtime Vec<i8> to spec Seq<int> */
spec fn vec_i8_to_seq(v: &Vec<i8>) -> Seq<int>
{
    v@.map_values(|x: i8| x as int)
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
    /* code modified by LLM (iteration 5): check spruce property and return corresponding String using String::from */
    let n_usize: usize = n as usize;
    let m: usize = parents.len();
    let mut has_child: Vec<bool> = vec![false; n_usize];

    let mut i: usize = 0;
    while i < m {
        let p = parents[i] as i32;
        let parent_idx = ((p - 1) as isize) as usize;
        if parent_idx < n_usize {
            has_child[parent_idx] = true;
        }
        i += 1;
    }

    let mut node: usize = 0;
    while node < n_usize {
        if has_child[node] {
            let mut leaf_count: i32 = 0;
            let mut j: usize = 0;
            while j < m {
                let p = parents[j] as i32;
                let parent_idx = ((p - 1) as isize) as usize;
                let child_idx = j + 1;
                if parent_idx == node && child_idx < n_usize && !has_child[child_idx] {
                    leaf_count += 1;
                }
                j += 1;
            }
            if leaf_count < 3 {
                return String::from("No");
            }
        }
        node += 1;
    }

    String::from("Yes")
}
// </vc-code>


}

fn main() {}