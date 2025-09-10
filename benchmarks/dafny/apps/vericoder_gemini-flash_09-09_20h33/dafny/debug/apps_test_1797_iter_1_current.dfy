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
  requires |visited| > 0
  ensures (0 <= find_unvisited(visited) < |visited| && !visited[find_unvisited(visited)]) || find_unvisited(visited) == -1
{
  var i := 0;
  while i < |visited|
    invariant 0 <= i <= |visited|
    invariant forall k :: 0 <= k < i ==> visited[k]
  {
    if !visited[i] then return i;
    i := i + 1;
  }
  return -1;
}

function get_cycle_length(p: seq<int>, visited: seq<bool>, start_node: int): int
  requires |p| == |visited|
  requires 0 <= start_node < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  ensures get_cycle_length(p, visited, start_node) > 0
{
  var current_node := start_node;
  var length := 0;
  while true
    invariant 0 <= current_node < |p|
    invariant length >= 0
    invariant forall k :: 0 <= k < length ==> current_node != start_node via p
  {
    current_node := p[current_node] - 1; // Adjust to 0-indexed
    length := length + 1;
    if current_node == start_node then return length;
  }
}

function mark_cycle_visited(p: seq<int>, visited: seq<bool>, start_node: int): seq<bool>
  requires |p| == |visited|
  requires 0 <= start_node < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  ensures |mark_cycle_visited(p, visited, start_node)| == |visited|
  ensures forall i :: 0 <= i < |visited| && visited[i] ==> mark_cycle_visited(p, visited, start_node)[i]
  ensures count_true(mark_cycle_visited(p, visited, start_node)) >= count_true(visited)
{
  var new_visited := visited;
  var current_node := start_node;
  while true
    invariant |new_visited| == |p|
    invariant (|visited| == |p|)
    invariant 0 <= current_node < |p|
    invariant forall k :: 0 <= k < |p| && (!visited[k] && new_visited[k]) ==> (exists l :: 0 <= l <= |p| && (current_node == p^l (start_node) -1) && (k == p^l (start_node) -1))
    invariant forall k :: 0 <= k < |p| && visited[k] ==> new_visited[k]
  {
    new_visited := new_visited[current_node := true];
    current_node := p[current_node] - 1; // Adjust to 0-indexed
    if current_node == start_node then return new_visited;
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
  var cycles := get_cycle_lengths(n, p);
  var s_sq := sum_of_squares(cycles);
  return s_sq;
}
// </vc-code>

