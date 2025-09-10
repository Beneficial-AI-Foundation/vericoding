predicate ValidInput(n: int, edges: seq<(int, int)>)
{
    n >= 2 &&
    forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n && edges[i].0 != edges[i].1
}

predicate ValidOutput(result: int, n: int, edges: seq<(int, int)>)
{
    result >= 0 && result <= 2 * |edges| * (|edges| + 1)
}

// <vc-helpers>
predicate is_connected_path(path: seq<int>, edges: seq<(int, int)>)
{
    |path| >= 1 &&
    (forall i :: 0 <= i < |path| ==> path[i] >= 1) &&
    (forall i :: 0 <= i < |path| - 1 ==> exists edge :: 0 <= edge < |edges| && 
        ((edges[edge].0 == path[i] && edges[edge].1 == path[i+1]) || (edges[edge].1 == path[i] && edges[edge].0 == path[i+1])))
}

function find_path_helper(start: int, target: int, edges: seq<(int, int)>, visited: set<int>, path: seq<int>, max_depth: int) : (result_path: seq<int>)
    decreases max_depth
    ensures is_connected_path(result_path, edges) || |result_path| == 0
{
    if start == target then
        return path + [start];
    if max_depth == 0 then
        return [];
    
    var next_visited := visited + {start};
    var current_path := path + [start];

    for edge_idx := 0 to |edges|-1 {
        var u := edges[edge_idx].0;
        var v := edges[edge_idx].1;

        if u == start && !(next_visited contains v) then
        {
            var found_path := find_path_helper(v, target, edges, next_visited, current_path, max_depth - 1);
            if |found_path| > 0 then
            {
                return found_path;
            }
        }
        else if v == start && !(next_visited contains u) then
        {
            var found_path := find_path_helper(u, target, edges, next_visited, current_path, max_depth - 1);
            if |found_path| > 0 then
            {
                return found_path;
            }
        }
    }
    return [];
}

function find_path(start: int, target: int, edges: seq<(int, int)>, n: int) : (result_path: seq<int>)
    ensures is_connected_path(result_path, edges) || |result_path| == 0
{
    find_path_helper(start, target, edges, {}, [], n * (n - 1) / 2) // Max depth based on number of nodes (a simple path can have at most n nodes, so n-1 edges)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, edges: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, edges)
    ensures ValidOutput(result, n, edges)
// </vc-spec>
// <vc-code>
{
    var max_triplets := 0;

    // Iterate through all possible ordered pairs of edges (e_1, e_2)
    for i := 0 to |edges| - 1 {
        var e1 := edges[i];
        var u1 := e1.0;
        var v1 := e1.1;

        for j := 0 to |edges| - 1 {
            var e2 := edges[j];
            var u2 := e2.0;
            var v2 := e2.1;

            // Iterate through all possible end nodes for the path (y)
            for y := 1 to n {
                // To form a triplet (x-e1), (e2-y), x and y must be distinct
                if u1 != y && v1 != y && u2 != y && v2 != y {
                     // Check if there is a path from an endpoint of e1 to an endpoint of e2
                     // that does not include y.
                    
                    var current_found_paths_count := 0;
                    
                    // Case 1: path from u1 to u2, avoiding y
                    if y != u1 && y != u2 {
                        var path_u1_u2 := find_path(u1, u2, edges, n);
                        if |path_u1_u2| > 0 && !(path_u1_u2 contains y) {
                            current_found_paths_count := current_found_paths_count + 1;
                        }
                    }

                    // Case 2: path from u1 to v2, avoiding y
                    if y != u1 && y != v2 {
                        var path_u1_v2 := find_path(u1, v2, edges, n);
                        if |path_u1_v2| > 0 && !(path_u1_v2 contains y) {
                            current_found_paths_count := current_found_paths_count + 1;
                        }
                    }
                    
                    // Case 3: path from v1 to u2, avoiding y
                    if y != v1 && y != u2 {
                        var path_v1_u2 := find_path(v1, u2, edges, n);
                        if |path_v1_u2| > 0 && !(path_v1_u2 contains y) {
                            current_found_paths_count := current_found_paths_count + 1;
                        }
                    }

                    // Case 4: path from v1 to v2, avoiding y
                    if y != v1 && y != v2 {
                        var path_v1_v2 := find_path(v1, v2, edges, n);
                        if |path_v1_v2| > 0 && !(path_v1_v2 contains y) {
                            current_found_paths_count := current_found_paths_count + 1;
                        }
                    }
                    max_triplets := max_triplets + current_found_paths_count;
                }
            }
        }
    }

    result := max_triplets;
}
// </vc-code>

