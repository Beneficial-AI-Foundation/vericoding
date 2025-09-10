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
function SimulateQueries(queries: seq<(char, int)>, up_to: int): BookshelfState
    requires 0 <= up_to < |queries|
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
{
    SimulateQueriesHelper(queries, up_to, BookshelfState(map[], 0, -1), 0)
}

function SimulateQueriesHelper(queries: seq<(char, int)>, up_to: int, state: BookshelfState, idx: int): BookshelfState
    requires 0 <= up_to < |queries|
    requires 0 <= idx <= up_to + 1
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    decreases up_to + 1 - idx
{
    if idx > up_to then state
    else
        var query := queries[idx];
        if query.0 == 'L' then
            var new_pos := state.head;
            var new_positions := state.positions[query.1 := new_pos];
            var new_state := BookshelfState(new_positions, new_pos - 1, state.tail);
            SimulateQueriesHelper(queries, up_to, new_state, idx + 1)
        else if query.0 == 'R' then
            var new_pos := state.tail + 1;
            var new_positions := state.positions[query.1 := new_pos];
            var new_state := BookshelfState(new_positions, state.head, new_pos);
            SimulateQueriesHelper(queries, up_to, new_state, idx + 1)
        else
            SimulateQueriesHelper(queries, up_to, state, idx + 1)
}

lemma SimulateQueriesBookExists(queries: seq<(char, int)>, up_to: int, book_id: int)
    requires 0 <= up_to < |queries|
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires exists j :: 0 <= j <= up_to && queries[j].0 in {'L', 'R'} && queries[j].1 == book_id
    ensures book_id in SimulateQueries(queries, up_to).positions
{
    SimulateQueriesHelperBookExists(queries, up_to, BookshelfState(map[], 0, -1), 0, book_id);
}

lemma SimulateQueriesHelperBookExists(queries: seq<(char, int)>, up_to: int, state: BookshelfState, idx: int, book_id: int)
    requires 0 <= up_to < |queries|
    requires 0 <= idx <= up_to + 1
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires exists j :: idx <= j <= up_to && queries[j].0 in {'L', 'R'} && queries[j].1 == book_id
    ensures book_id in SimulateQueriesHelper(queries, up_to, state, idx).positions
    decreases up_to + 1 - idx
{
    if idx > up_to {
        return;
    }
    
    var query := queries[idx];
    if query.0 == 'L' {
        if query.1 == book_id {
            return;
        } else {
            SimulateQueriesHelperBookExists(queries, up_to, BookshelfState(state.positions[query.1 := state.head], state.head - 1, state.tail), idx + 1, book_id);
        }
    } else if query.0 == 'R' {
        if query.1 == book_id {
            return;
        } else {
            SimulateQueriesHelperBookExists(queries, up_to, BookshelfState(state.positions[query.1 := state.tail + 1], state.head, state.tail + 1), idx + 1, book_id);
        }
    } else {
        SimulateQueriesHelperBookExists(queries, up_to, state, idx + 1, book_id);
    }
}

function CountQuestionMarks(queries: seq<(char, int)>): int
{
    CountQuestionMarksHelper(queries, 0)
}

function CountQuestionMarksHelper(queries: seq<(char, int)>, idx: int): int
    requires 0 <= idx <= |queries|
    decreases |queries| - idx
{
    if idx >= |queries| then 0
    else if queries[idx].0 == '?' then 1 + CountQuestionMarksHelper(queries, idx + 1)
    else CountQuestionMarksHelper(queries, idx + 1)
}

lemma CountQuestionMarksCorrect(queries: seq<(char, int)>)
    ensures CountQuestionMarks(queries) == |set i | 0 <= i < |queries| && queries[i].0 == '?'|
{
    CountQuestionMarksHelperCorrect(queries, 0);
}

lemma CountQuestionMarksHelperCorrect(queries: seq<(char, int)>, start: int)
    requires 0 <= start <= |queries|
    ensures CountQuestionMarksHelper(queries, start) == |set i | start <= i < |queries| && queries[i].0 == '?'|
    decreases |queries| - start
{
    if start >= |queries| {
        assert (set i | start <= i < |queries| && queries[i].0 == '?') == {};
    } else {
        CountQuestionMarksHelperCorrect(queries, start + 1);
        var rest_set := set i | start + 1 <= i < |queries| && queries[i].0 == '?';
        var full_set := set i | start <= i < |queries| && queries[i].0 == '?';
        
        if queries[start].0 == '?' {
            assert full_set == {start} + rest_set;
            assert start !in rest_set;
        } else {
            assert full_set == rest_set;
        }
    }
}

function CollectResults(queries: seq<(char, int)>, idx: int, acc: seq<int>): seq<int>
    requires 0 <= idx <= |queries|
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires forall i :: 0 <= i < |queries| && queries[i].0 == '?' ==> 
        exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1
    decreases |queries| - idx
{
    if idx >= |queries| then acc
    else if queries[idx].0 == '?' then
        var result := ComputeMinRemovals(queries, idx);
        CollectResults(queries, idx + 1, acc + [result])
    else
        CollectResults(queries, idx + 1, acc)
}

lemma CollectResultsLength(queries: seq<(char, int)>, idx: int, acc: seq<int>)
    requires ValidInput(queries)
    requires 0 <= idx <= |queries|
    ensures |CollectResults(queries, idx, acc)| == |acc| + |set i | idx <= i < |queries| && queries[i].0 == '?'|
    decreases |queries| - idx
{
    if idx >= |queries| {
        assert (set i | idx <= i < |queries| && queries[i].0 == '?') == {};
    } else {
        CollectResultsLength(queries, idx + 1, acc);
        var rest_set := set i | idx + 1 <= i < |queries| && queries[i].0 == '?';
        var full_set := set i | idx <= i < |queries| && queries[i].0 == '?';
        
        if queries[idx].0 == '?' {
            CollectResultsLength(queries, idx + 1, acc + [ComputeMinRemovals(queries, idx)]);
            assert full_set == {idx} + rest_set;
            assert idx !in rest_set;
            assert |full_set| == 1 + |rest_set|;
        } else {
            CollectResultsLength(queries, idx + 1, acc);
            assert full_set == rest_set;
        }
    }
}

lemma CollectResultsValid(queries: seq<(char, int)>)
    requires ValidInput(queries)
    ensures ValidOutput(queries, CollectResults(queries, 0, []))
{
    var results := CollectResults(queries, 0, []);
    CollectResultsLength(queries, 0, []);
    CountQuestionMarksCorrect(queries);
    assert |results| == |set i | 0 <= i < |queries| && queries[i].0 == '?'|;
    
    CollectResultsNonNegative(queries, 0, []);
    CollectResultsContainsAll(queries, 0, []);
    CollectResultsAllFromQueries(queries, 0, []);
}

lemma CollectResultsNonNegative(queries: seq<(char, int)>, idx: int, acc: seq<int>)
    requires ValidInput(queries)
    requires 0 <= idx <= |queries|
    requires forall i :: 0 <= i < |acc| ==> acc[i] >= 0
    ensures forall i :: 0 <= i < |CollectResults(queries, idx, acc)| ==> CollectResults(queries, idx, acc)[i] >= 0
    decreases |queries| - idx
{
    if idx >= |queries| {
        return;
    }
    
    if queries[idx].0 == '?' {
        var result := ComputeMinRemovals(queries, idx);
        ComputeMinRemovalsNonNegative(queries, idx);
        CollectResultsNonNegative(queries, idx + 1, acc + [result]);
    } else {
        CollectResultsNonNegative(queries, idx + 1, acc);
    }
}

lemma ComputeMinRemovalsNonNegative(queries: seq<(char, int)>, query_idx: int)
    requires ValidInput(queries)
    requires 0 <= query_idx < |queries|
    requires queries[query_idx].0 == '?'
    ensures ComputeMinRemovals(queries, query_idx) >= 0
{
    var book_id := queries[query_idx].1;
    assert exists j :: 0 <= j < query_idx && queries[j].0 in {'L', 'R'} && queries[j].1 == book_id;
    SimulateQueriesBookExists(queries, query_idx - 1, book_id);
}

lemma CollectResultsContainsAll(queries: seq<(char, int)>, idx: int, acc: seq<int>)
    requires ValidInput(queries)
    requires 0 <= idx <= |queries|
    ensures forall q_idx :: idx <= q_idx < |queries| && queries[q_idx].0 == '?' ==>
        exists r_idx :: 0 <= r_idx < |CollectResults(queries, idx, acc)| &&
        CollectResults(queries, idx, acc)[r_idx] == ComputeMinRemovals(queries, q_idx)
    decreases |queries| - idx
{
    if idx >= |queries| {
        return;
    }
    
    if queries[idx].0 == '?' {
        var new_acc := acc + [ComputeMinRemovals(queries, idx)];
        CollectResultsContainsAll(queries, idx + 1, new_acc);
        forall q_idx | idx <= q_idx < |queries| && queries[q_idx].0 == '?'
            ensures exists r_idx :: 0 <= r_idx < |CollectResults(queries, idx, acc)| &&
                CollectResults(queries, idx, acc)[r_idx] == ComputeMinRemovals(queries, q_idx)
        {
            if q_idx == idx {
                assert CollectResults(queries, idx, acc)[|acc|] == ComputeMinRemovals(queries, idx);
            } else {
                var results_from_next := CollectResults(queries, idx + 1, new_acc);
                assert CollectResults(queries, idx, acc) == results_from_next;
            }
        }
    } else {
        CollectResultsContainsAll(queries, idx + 1, acc);
    }
}

lemma CollectResultsAllFromQueries(queries: seq<(char, int)>, idx: int, acc: seq<int>)
    requires ValidInput(queries)
    requires 0 <= idx <= |queries|
    ensures forall r_idx {:trigger CollectResults(queries, idx, acc)[r_idx]} :: |acc| <= r_idx < |CollectResults(queries, idx, acc)| ==>
        exists q_idx :: idx <= q_idx < |queries| && queries[q_idx].0 == '?' &&
        CollectResults(queries, idx, acc)[r_idx] == ComputeMinRemovals(queries, q_idx)
    decreases |queries| - idx
{
    if idx >= |queries| {
        return;
    }
    
    if queries[idx].0 == '?' {
        var new_acc := acc + [ComputeMinRemovals(queries, idx)];
        CollectResultsAllFromQueries(queries, idx + 1, new_acc);
        
        forall r_idx | |acc| <= r_idx < |CollectResults(queries, idx, acc)|
            ensures exists q_idx :: idx <= q_idx < |queries| && queries[q_idx].0 == '?' &&
                CollectResults(queries, idx, acc)[r_idx] == ComputeMinRemovals(queries, q_idx)
        {
            if r_idx == |acc| {
                assert CollectResults(queries, idx, acc)[r_idx] == ComputeMinRemovals(queries, idx);
            } else {
                assert r_idx > |acc|;
                assert r_idx >= |new_acc|;
            }
        }
    } else {
        CollectResultsAllFromQueries(queries, idx + 1, acc);
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
    results := CollectResults(queries, 0, []);
    CollectResultsValid(queries);
}
// </vc-code>

