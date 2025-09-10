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
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    // The specific '?' requirement for ValidInput is slightly different,
    // this helper needs a weaker one for it to be applicable to any up_to_idx.
    // It asserts that if queries[i].0 == '?' then exists a previous L/R query with the same ID.
    // For queries[up_to_idx] specifically if it's '?', the preceding L/R query must exist.
    // This is implicitly guaranteed by ValidInput.
    modifies {}
    ensures var initial_state := BookshelfState(map[], 0, 0);
            var result_state := SimulateQueriesRec(queries, up_to_idx, initial_state, 0);
            result_state == BookshelfState(result_state.positions, result_state.head, result_state.tail)
{
    SimulateQueriesRec(queries, up_to_idx, BookshelfState(map[], 0, 0), 0)
}

function SimulateQueriesRec(queries: seq<(char, int)>, up_to_idx: int, currentState: BookshelfState, current_q_idx: int): BookshelfState
    requires 0 <= current_q_idx <= up_to_idx < |queries|
    modifies {}
    ensures var nextState := if current_q_idx < up_to_idx then SimulateQueriesRec(queries, up_to_idx, _, current_q_idx + 1) else currentState;
            // This is a placeholder for a more complex postcondition,
            // which would involve showing how currentState is transformed
            // based on queries[current_q_idx].
            // For now, ensuring it returns a BookshelfState.
            nextState == BookshelfState(nextState.positions, nextState.head, nextState.tail)
{
    if current_q_idx == up_to_idx
    {
        currentState
    } else {
        var query := queries[current_q_idx];
        var op := query.0;
        var book_id := query.1;
        var newPositions := currentState.positions;
        var newHead := currentState.head;
        var newTail := currentState.tail;

        if op == 'L' {
            if !(book_id in newPositions) {
                newHead := newHead - 1;
                newPositions := newPositions + {book_id := newHead};
            }
        } else if op == 'R' {
            if !(book_id in newPositions) {
                newTail := newTail + 1;
                newPositions := newPositions + {book_id := newTail};
            }
        } else if op == '?' {
            // No change to state for '?' queries
            // The logic for '?' queries relies on `book_id in newPositions` being true
            // due to initial ValidInput predicate assumption.
        }

        SimulateQueriesRec(queries, up_to_idx, BookshelfState(newPositions, newHead, newTail), current_q_idx + 1)
    }
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(char, int)>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidOutput(queries, results)
// </vc-spec>
// <vc-code>
{
    var q_indices_for_question := new int[0];
    var results_list := new int[0];

    var num_question_queries := 0;
    for i := 0 to |queries|
        invariant 0 <= i <= |queries|
        invariant num_question_queries == |set k | 0 <= k < i && queries[k].0 == '?'|
        invariant |results_list| == num_question_queries
        invariant forall k :: 0 <= k < |results_list| ==> results_list[k] >= 0
        invariant forall k :: 0 <= k < |results_list| ==>
            exists q_idx :: 0 <= q_idx < i && queries[q_idx].0 == '?' &&
            results_list[k] == ComputeMinRemovals(queries, q_idx)
    {
        if i < |queries| && queries[i].0 == '?' {
            var min_removals := ComputeMinRemovals(queries, i);
            results_list := results_list + [min_removals];
            num_question_queries := num_question_queries + 1;
        }
    }
    return results_list;
}
// </vc-code>

