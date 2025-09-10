predicate ValidInput(queries: seq<(char, int)>)
{
    && |queries| > 0
    && (forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'})
    && (forall i :: 0 <= i < |queries| ==> queries[i].1 > 0)
    && (forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1)
    && (forall i :: 0 <= i < |queries| && queries[i].0 == '?' ==> 
        exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1)
    && (exists i :: 0 <= i < |queries| && queries[i].0 == '?')
}

predicate ValidOutput(queries: seq<(char, int)>, results: seq<int>)
    requires ValidInput(queries)
{
    && |results| == |set i | 0 <= i < |queries| && queries[i].0 == '?'|
    && (forall i :: 0 <= i < |results| ==> results[i] >= 0)
    && (forall r_idx :: 0 <= r_idx < |results| ==> 
        (exists q_idx :: 0 <= q_idx < |queries| && queries[q_idx].0 == '?' &&
         results[r_idx] == ComputeMinRemovals(queries, q_idx)))
    && (forall q_idx :: 0 <= q_idx < |queries| && queries[q_idx].0 == '?' ==>
        (exists r_idx :: 0 <= r_idx < |results| &&
         results[r_idx] == ComputeMinRemovals(queries, q_idx)))
}

datatype BookshelfState = BookshelfState(positions: map<int, int>, head: int, tail: int)

function ComputeMinRemovals(queries: seq<(char, int)>, query_idx: int): int
    requires 0 <= query_idx < |queries|
    requires queries[query_idx].0 == '?'
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires forall i :: 0 <= i < |queries| && queries[i].0 == '?' ==> 
        exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1
{
    var book_id := queries[query_idx].1;
    var state := SimulateQueries(queries, query_idx);
    assert book_id in state.positions;
    var pos := state.positions[book_id];
    var left_removals := pos - state.head;
    var right_removals := state.tail - pos;
    var min_removals := if left_removals <= right_removals then left_removals else right_removals;
    min_removals - 1
}

// <vc-helpers>
function SimulateQueries(queries: seq<(char, int)>, up_to_idx: int): BookshelfState
    requires 0 <= up_to_idx < |queries|
    // The following `requires` clauses are taken directly from the problem description
    // and should be sufficient to ensure correctness of the simulation.
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires forall i :: 0 <= i < up_to_idx && queries[i].0 == '?' ==> exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1
    requires queries[up_to_idx].0 == '?' ==> (exists j :: 0 <= j < up_to_idx && queries[j].0 in {'L','R'} && queries[j].1 == queries[up_to_idx].1)
{
    SimulateQueriesRec(queries, up_to_idx, BookshelfState(map[], 0, 0), 0)
}

function SimulateQueriesRec(queries: seq<(char, int)>, up_to_idx: int, currentState: BookshelfState, current_q_idx: int): BookshelfState
    requires 0 <= current_q_idx <= up_to_idx < |queries|
    // The following `requires` clauses are inherited from `SimulateQueries` or are inductive.
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires forall i :: 0 <= i < up_to_idx && queries[i].0 == '?' ==> exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1
    requires queries[up_to_idx].0 == '?' ==> (exists j :: 0 <= j < up_to_idx && queries[j].0 in {'L','R'} && queries[j].1 == queries[up_to_idx].1)
    decreases up_to_idx - current_q_idx
{
    if current_q_idx == up_to_idx then
    (
        currentState
    ) else (
        var query := queries[current_q_idx];
        var op := query.0;
        var book_id := query.1;
        var newPositions := currentState.positions;
        var newHead := currentState.head;
        var newTail := currentState.tail;

        if op == 'L' then (
            if !(book_id in newPositions) then (
                newHead := newHead - 1;
                newPositions := newPositions + {book_id := newHead};
            )
        ) else if op == 'R' then (
            if !(book_id in newPositions) then (
                newTail := newTail + 1;
                newPositions := newPositions + {book_id := newTail};
            )
        )
        // No change to state for '?' queries when simulating forward.
        // The `ComputeMinRemovals` function handles the '?' queries where it actually needs to
        // look up the book_id. Here we only build up the state of definitive L/R operations.

        SimulateQueriesRec(queries, up_to_idx, BookshelfState(newPositions, newHead, newTail), current_q_idx + 1)
    )
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(char, int)>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidOutput(queries, results)
// </vc-spec>
// <vc-code>
{
    var results_list: seq<int> := [];

    var q_count := 0; 
    for i := 0 to |queries|-1
    {
        if queries[i].0 == '?' {
            var min_removals := ComputeMinRemovals(queries, i);
            results_list := results_list + [min_removals];
            q_count := q_count + 1;
        }
    }
    return results_list;
}
// </vc-code>

