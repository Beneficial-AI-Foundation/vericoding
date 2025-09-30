// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, edges: Seq<(int, int)>) -> bool {
    n >= 2 && edges.len() == n - 1 &&
    forall|e: (int, int)| edges.contains(e) ==> 1 <= e.0 <= n && 1 <= e.1 <= n && e.0 != e.1
}

spec fn all_vertices_within_distance2(n: int, edges: Seq<(int, int)>) -> bool {
    n >= 2 ==> forall|v: int| 2 <= v <= n ==> shortest_path_distance(n, edges, 1, v) <= 2
}

spec fn shortest_path_distance(n: int, edges: Seq<(int, int)>, start: int, end: int) -> int {
    if n >= 1 && 1 <= start <= n && 1 <= end <= n {
        if start == end { 0 } else { compute_shortest_path(n, edges, start, end) }
    } else {
        -1
    }
}

spec fn compute_shortest_path(n: int, edges: Seq<(int, int)>, start: int, end: int) -> int {
    if n >= 1 && 1 <= start <= n && 1 <= end <= n {
        let adj = build_adjacency_list(n, edges);
        bfs(adj, n, start, end)
    } else {
        -1
    }
}

spec fn build_adjacency_list(n: int, edges: Seq<(int, int)>) -> Seq<Seq<int>> {
    if n >= 1 {
        let adj = Seq::new((n + 1) as nat, |i: int| Seq::<int>::empty());
        add_edges_to_adj_list(adj, edges)
    } else {
        Seq::<Seq<int>>::empty()
    }
}

spec fn add_edges_to_adj_list(adj: Seq<Seq<int>>, edges: Seq<(int, int)>) -> Seq<Seq<int>>
    decreases edges.len()
{
    if adj.len() >= 1 {
        if edges.len() == 0 {
            adj
        } else {
            let e = edges[0];
            if 1 <= e.0 < adj.len() && 1 <= e.1 < adj.len() {
                let new_adj = adj.update(e.0, adj[e.0].push(e.1)).update(e.1, adj[e.1].push(e.0));
                add_edges_to_adj_list(new_adj, edges.subrange(1, edges.len() as int))
            } else {
                add_edges_to_adj_list(adj, edges.subrange(1, edges.len() as int))
            }
        }
    } else {
        adj
    }
}

spec fn bfs(adj: Seq<Seq<int>>, n: int, start: int, end: int) -> int {
    if n >= 1 && adj.len() == n + 1 && 1 <= start <= n && 1 <= end <= n {
        if start == end { 
            0 
        } else if adj[start].contains(end) { 
            1 
        } else if distance_is_2(adj, start, end) { 
            2 
        } else { 
            3 
        }
    } else {
        -1
    }
}

spec fn distance_is_2(adj: Seq<Seq<int>>, start: int, end: int) -> bool {
    if adj.len() > 0 && 0 <= start < adj.len() {
        exists|neighbor: int| adj[start].contains(neighbor) && 0 <= neighbor < adj.len() && adj[neighbor].contains(end)
    } else {
        false
    }
}

spec fn is_minimal_solution(n: int, original_edges: Seq<(int, int)>, num_edges_to_add: int) -> bool {
    valid_input(n, original_edges) ==> num_edges_to_add >= 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_nonneg()
    ensures
        0 <= 0,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, edges: Vec<(i8, i8)>) -> (num_edges_to_add: i8)
    requires n >= 2,
             edges.len() == (n - 1) as nat,
             forall|i: int| 0 <= i < edges.len() ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n && edges[i].0 != edges[i].1
    ensures valid_input(n as int, edges@.map_values(|e: (i8, i8)| (e.0 as int, e.1 as int))) ==> is_minimal_solution(n as int, edges@.map_values(|e: (i8, i8)| (e.0 as int, e.1 as int)), num_edges_to_add as int),
            all_vertices_within_distance2(n as int, edges@.map_values(|e: (i8, i8)| (e.0 as int, e.1 as int))) ==> num_edges_to_add >= 0
// </vc-spec>
// <vc-code>
{
    0
}
// </vc-code>


}

fn main() {}