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

proof fn lemma_valid_children_properties(n: int, parents: Seq<int>)
    requires
        valid_input(n, parents),
    ensures
        forall|node: int| 0 <= node < n && has_children(node, parents, n) ==>
            count_leaf_children(node, parents, n) >= 3,
{
    /* helper modified by LLM (iteration 4): simplified to match is_spruce definition */
}

proof fn lemma_sequence_bounds(n: int, parents: Seq<int>)
    requires
        valid_input(n, parents),
    ensures
        forall|i: int| 0 <= i < parents.len() ==> 0 <= parents[i] - 1 < n,
{
    /* helper modified by LLM (iteration 4): kept same */
}

spec fn count_leaves_recursive(start: int, n: int, parents: Seq<int>) -> int
    recommends 0 <= start < n, valid_input(n, parents)
{
    /* helper modified by LLM (iteration 4): replaced fold with explicit sum */
    if !has_children(start, parents, n) {
        1
    } else {
        let mut sum = 0;
        for i in 0..parents.len() {
            if parents[i] - 1 == start {
                sum = sum + count_leaves_recursive(i + 1, n, parents);
            }
        }
        sum
    }
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
    /* code modified by LLM (iteration 4): fixed compilation error by avoiding Seq.fold */
    let mut result = String::new();
    
    if n < 3 {
        result = "No".to_string();
    } else {
        let n_usize = n as usize;
        let mut children_count = vec![0; n_usize];
        let mut leaf_count = vec![0; n_usize];
        
        for i in 0..(n - 1) as usize {
            let parent = parents[i] as usize - 1;
            children_count[parent] += 1;
        }
        
        let mut node = n_usize;
        while node > 0 {
            node -= 1;
            if children_count[node] == 0 {
                leaf_count[node] = 1;
            } else {
                let mut total_leaves = 0;
                for i in 0..(n - 1) as usize {
                    if parents[i] as usize - 1 == node {
                        let child = i + 1;
                        total_leaves += leaf_count[child];
                    }
                }
                leaf_count[node] = total_leaves;
                
                if leaf_count[node] < 3 {
                    result = "No".to_string();
                    break;
                }
            }
        }
        
        if result.is_empty() {
            result = "Yes".to_string();
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}