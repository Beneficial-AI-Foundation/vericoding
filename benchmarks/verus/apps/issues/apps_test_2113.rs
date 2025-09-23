// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn is_connected_tree(n: int, edges: Seq<(int, int)>) -> bool {
        n >= 1 && edges.len() == n - 1 &&
        (n == 1 ==> edges.len() == 0) &&
        (n > 1 ==> is_connected_graph(n, edges))
    }
    
    spec fn is_connected_graph(n: int, edges: Seq<(int, int)>) -> bool {
        n > 1 ==>
        (forall|node: int| 2 <= node <= n ==> 
            can_reach_node_one(node, edges, n))
    }
    
    spec fn can_reach_node_one(target: int, edges: Seq<(int, int)>, max_depth: int) -> bool
        decreases max_depth
    {
        if max_depth <= 0 { 
            false
        } else if target == 1 { 
            true
        } else {
            exists|i: int| 0 <= i < edges.len() && 
                ((edges[i].0 == target && can_reach_node_one(edges[i].1, edges, max_depth - 1)) ||
                 (edges[i].1 == target && can_reach_node_one(edges[i].0, edges, max_depth - 1)))
        }
    }
    
    spec fn valid_tree_input(n: int, edges: Seq<(int, int)>) -> bool {
        n >= 1 &&
        edges.len() == n - 1 &&
        (forall|i: int| #[trigger] edges.index(i).0 == edges[i].0 && 0 <= i < edges.len() ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n) &&
        (forall|i: int| #[trigger] edges.index(i).0 == edges[i].0 && 0 <= i < edges.len() ==> edges[i].0 != edges[i].1) &&
        (forall|i: int, j: int| #[trigger] edges.index(i).0 == edges[i].0 && #[trigger] edges.index(j).0 == edges[j].0 && 0 <= i < j < edges.len() ==> 
            !(edges[i].0 == edges[j].0 && edges[i].1 == edges[j].1) && 
            !(edges[i].0 == edges[j].1 && edges[i].1 == edges[j].0)) &&
        (n == 1 ==> edges.len() == 0) &&
        (n > 1 ==> (forall|node: int| #[trigger] (node + 1 - 1) == node && 1 <= node <= n ==> 
            (exists|i: int| 0 <= i < edges.len() && (edges[i].0 == node || edges[i].1 == node)))) &&
        is_connected_tree(n, edges)
    }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, edges: Vec<(i8, i8)>) -> (result: i8)
    requires
        valid_tree_input(n as int, Seq::from_vec(edges).map(|i, e| (e.0 as int, e.1 as int))),
    ensures
        result >= 0,
        exists|blue: int, red: int| #[trigger] (blue + red) == (blue + red) &&
            blue >= 0 && red >= 0 && blue + red == n as int && result as int == blue * red - (n as int - 1),
        n == 1 ==> result == 0,
        n == 2 ==> result == 0,
        n > 2 ==> exists|blue: int, red: int| #[trigger] (blue + red) == (blue + red) &&
            blue > 0 && red > 0 && blue + red == n as int && result as int == blue * red - (n as int - 1),
        result as int <= (n as int * n as int) / 4 - (n as int - 1) + (if n % 2 == 0 { 0int } else { 1int }),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}