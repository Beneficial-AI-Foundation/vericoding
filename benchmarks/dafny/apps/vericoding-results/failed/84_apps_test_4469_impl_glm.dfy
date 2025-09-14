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
function SimulateQueries(queries: seq<(char, int)>, upTo: int): BookshelfState
    requires 0 <= upTo <= |queries|
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires forall i :: 0 <= i < |queries| && queries[i].0 == '?' ==> 
        exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1
{
    if upTo == 0 then
        BookshelfState(map[], 0, 0)
    else
        var prev_state := SimulateQueries(queries, upTo - 1);
        var query := queries[upTo - 1];
        var book_id := query.1;
        var action := query.0;

        if action == 'L' then
            var new_positions := prev_state.positions[book_id := prev_state.tail];
            BookshelfState(new_positions, prev_state.head, prev_state.tail + 1)
        else if action == 'R' then
            var new_positions := prev_state.positions[book_id := prev_state.head - 1];
            BookshelfState(new_positions, prev_state.head - 1, prev_state.tail)
        else // action == '?'
            assert book_id in prev_state.positions;
            prev_state
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(char, int)>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidOutput(queries, results)
// </vc-spec>
// <vc-code>
{
    var state := BookshelfState(map[], 0, 0);
    results := [];
    var i := 0;

    while i < |queries|
        invariant 0 <= i <= |queries|
        invariant |results| == |set j | 0 <= j < i && queries[j].0 == '?'|
        invariant forall r_idx :: 0 <= r_idx < |results| ==> results[r_idx] >= 0
        invariant forall j :: 0 <= j < |results| ==>
            exists q_idx :: 0 <= q_idx < i && queries[q_idx].0 == '?' && results[j] == ComputeMinRemovals(queries, q_idx)
        invariant forall q_idx :: 0 <= q_idx < i && queries[q_idx].0 == '?' ==>
            exists r_idx :: 0 <= r_idx < |results| && results[r_idx] == ComputeMinRemovals(queries, q_idx)
        invariant state == SimulateQueries(queries, i)
    {
        if queries[i].0 == '?' {
            var book_id := queries[i].1;
            var pos := state.positions[book_id];
            var left_removals := pos - state.head;
            var right_removals := state.tail - pos;
            var min_removals := if left_removals <= right_removals then left_removals else right_removals;
            results := results + [min_removals - 1];
            i := i + 1;
        } else if queries[i].0 == 'L' {
            var book_id := queries[i].1;
            state := BookshelfState(state.positions[book_id := state.tail], state.head, state.tail + 1);
            i := i + 1;
        } else {
            // must be 'R'
            var book_id := queries[i].1;
            state := BookshelfState(state.positions[book_id := state.head - 1], state.head - 1, state.tail);
            i := i + 1;
        }
    }
    return results;
}
// </vc-code>

