predicate ValidInput(n: int, p: seq<int>)
{
  n > 0 && |p| == n &&
  (forall i :: 0 <= i < n ==> 1 <= p[i] <= n) &&
  (forall i, j :: 0 <= i < j < n ==> p[i] != p[j])
}

function count_true(visited: seq<bool>): int
  ensures count_true(visited) >= 0
  ensures count_true(visited) <= |visited|
{
  if |visited| == 0 then 0
  else (if visited[0] then 1 else 0) + count_true(visited[1..])
}

function sum_of_squares(s: seq<int>): int 
{
  if |s| == 0 then 0 else s[0] * s[0] + sum_of_squares(s[1..])
}

function get_cycle_lengths(n: int, p: seq<int>): seq<int>
  requires ValidInput(n, p)
{
  get_cycles_helper(n, p, seq(n, i => false), [])
}

function get_cycles_helper(n: int, p: seq<int>, visited: seq<bool>, cycles: seq<int>): seq<int>
  requires n > 0
  requires |p| == n
  requires |visited| == n
  requires forall i :: 0 <= i < n ==> 1 <= p[i] <= n
  requires forall i, j :: 0 <= i < j < n ==> p[i] != p[j]
  decreases n - count_true(visited)
{
  if count_true(visited) >= n then cycles
  else
    var unvisited := find_unvisited(visited);
    if unvisited == -1 then cycles
    else if 0 <= unvisited < n then
      var cycle_length := get_cycle_length(p, visited, unvisited);
      var new_visited := mark_cycle_visited(p, visited, unvisited);
      if count_true(new_visited) > count_true(visited) && count_true(new_visited) <= n then
        get_cycles_helper(n, p, new_visited, cycles + [cycle_length])
      else
        cycles + [cycle_length]
    else
      cycles
}

// <vc-helpers>
function find_unvisited(visited: seq<bool>): int
  ensures -1 <= find_unvisited(visited) < |visited|
  ensures find_unvisited(visited) >= 0 ==> !visited[find_unvisited(visited)]
  ensures find_unvisited(visited) == -1 ==> forall i :: 0 <= i < |visited| ==> visited[i]
{
  find_unvisited_helper(visited, 0)
}

function find_unvisited_helper(visited: seq<bool>, index: int): int
  requires 0 <= index <= |visited|
  ensures -1 <= find_unvisited_helper(visited, index) < |visited|
  ensures find_unvisited_helper(visited, index) >= 0 ==> find_unvisited_helper(visited, index) >= index
  ensures find_unvisited_helper(visited, index) >= 0 ==> !visited[find_unvisited_helper(visited, index)]
  ensures find_unvisited_helper(visited, index) == -1 ==> forall i :: index <= i < |visited| ==> visited[i]
  decreases |visited| - index
{
  if index >= |visited| then -1
  else if !visited[index] then index
  else find_unvisited_helper(visited, index + 1)
}

function get_cycle_length(p: seq<int>, visited: seq<bool>, start: int): int
  requires |p| == |visited|
  requires 0 <= start < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  ensures get_cycle_length(p, visited, start) >= 1
{
  get_cycle_length_helper(p, visited, start, start, 1)
}

function get_cycle_length_helper(p: seq<int>, visited: seq<bool>, start: int, current: int, length: int): int
  requires |p| == |visited|
  requires 0 <= start < |p|
  requires 0 <= current < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires length >= 1
  ensures get_cycle_length_helper(p, visited, start, current, length) >= 1
  decreases |p| - length
{
  var next := p[current] - 1;
  if next == start then length
  else if 0 <= next < |p| && length < |p| then
    get_cycle_length_helper(p, visited, start, next, length + 1)
  else
    length
}

function mark_cycle_visited(p: seq<int>, visited: seq<bool>, start: int): seq<bool>
  requires |p| == |visited|
  requires 0 <= start < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  ensures |mark_cycle_visited(p, visited, start)| == |visited|
  ensures forall i :: 0 <= i < |visited| && visited[i] ==> mark_cycle_visited(p, visited, start)[i]
{
  var cycle_len := get_cycle_length(p, visited, start);
  mark_cycle_visited_helper(p, visited, start, start, cycle_len)
}

function mark_cycle_visited_helper(p: seq<int>, visited: seq<bool>, start: int, current: int, remaining: int): seq<bool>
  requires |p| == |visited|
  requires 0 <= start < |p|
  requires 0 <= current < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires remaining >= 0
  ensures |mark_cycle_visited_helper(p, visited, start, current, remaining)| == |visited|
  ensures forall i :: 0 <= i < |visited| && visited[i] ==> mark_cycle_visited_helper(p, visited, start, current, remaining)[i]
  decreases remaining
{
  if remaining == 0 then visited
  else if 0 <= current < |visited| then
    var next := p[current] - 1;
    var new_visited := visited[current := true];
    if 0 <= next < |p| then
      mark_cycle_visited_helper(p, new_visited, start, next, remaining - 1)
    else
      new_visited
  else
    visited
}

lemma sum_of_squares_positive(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  requires |s| > 0
  ensures sum_of_squares(s) > 0
{
  if |s| == 1 {
    assert s[0] >= 1;
    assert s[0] * s[0] >= 1;
    assert sum_of_squares(s) == s[0] * s[0] >= 1;
  } else {
    assert s[0] >= 1;
    assert s[0] * s[0] >= 1;
    if |s[1..]| > 0 {
      sum_of_squares_positive(s[1..]);
    }
  }
}

lemma get_cycles_helper_positive(n: int, p: seq<int>, visited: seq<bool>, cycles: seq<int>)
  requires n > 0
  requires |p| == n
  requires |visited| == n
  requires forall i :: 0 <= i < n ==> 1 <= p[i] <= n
  requires forall i, j :: 0 <= i < j < n ==> p[i] != p[j]
  requires forall i :: 0 <= i < |cycles| ==> cycles[i] >= 1
  ensures forall i :: 0 <= i < |get_cycles_helper(n, p, visited, cycles)| ==> get_cycles_helper(n, p, visited, cycles)[i] >= 1
  decreases n - count_true(visited)
{
  if count_true(visited) >= n {
    // Base case: all visited, return cycles
  } else {
    var unvisited := find_unvisited(visited);
    if unvisited == -1 {
      // No unvisited, return cycles
    } else if 0 <= unvisited < n {
      var cycle_length := get_cycle_length(p, visited, unvisited);
      assert cycle_length >= 1;
      var new_visited := mark_cycle_visited(p, visited, unvisited);
      if count_true(new_visited) > count_true(visited) && count_true(new_visited) <= n {
        var new_cycles := cycles + [cycle_length];
        assert forall i :: 0 <= i < |cycles| ==> new_cycles[i] == cycles[i] >= 1;
        assert new_cycles[|new_cycles| - 1] == cycle_length >= 1;
        assert forall i :: 0 <= i < |new_cycles| ==> new_cycles[i] >= 1;
        get_cycles_helper_positive(n, p, new_visited, new_cycles);
      } else {
        var result := cycles + [cycle_length];
        assert forall i :: 0 <= i < |cycles| ==> result[i] == cycles[i] >= 1;
        assert result[|result| - 1] == cycle_length >= 1;
        assert forall i :: 0 <= i < |result| ==> result[i] >= 1;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
  requires ValidInput(n, p)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  var cycle_lengths := get_cycle_lengths(n, p);
  
  // Prove that all cycle lengths are positive
  var initial_visited := seq(n, i => false);
  var initial_cycles: seq<int> := [];
  assert cycle_lengths == get_cycles_helper(n, p, initial_visited, initial_cycles);
  get_cycles_helper_positive(n, p, initial_visited, initial_cycles);
  assert forall i :: 0 <= i < |cycle_lengths| ==> cycle_lengths[i] >= 1;
  
  if |cycle_lengths| == 0 {
    result := 1;
  } else {
    sum_of_squares_positive(cycle_lengths);
    result := sum_of_squares(cycle_lengths);
  }
}
// </vc-code>

