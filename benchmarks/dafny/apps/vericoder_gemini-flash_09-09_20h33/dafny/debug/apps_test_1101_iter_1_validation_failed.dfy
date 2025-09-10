predicate isValidPlacement(rooms: string, k: int, placement: seq<int>)
{
    |placement| == k + 1 &&
    (forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms|) &&
    (forall i :: 0 <= i < |placement| ==> rooms[placement[i]] == '0') &&
    (forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]) &&
    (forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1])
}

// <vc-helpers>
predicate optimalMaxDistance(placement: seq<int>)
{
  0 < |placement| &&
  (forall i :: 0 <= i < |placement| -1 ==> placement[i+1] - placement[i] <= placement[0] + (|placement| > 1 ? placement[|placement|-1] - placement[1] : 0))
  // This predicate is tricky. The `optimalMaxDistance`
  // mentioned in the postcondition `ensures exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) == result`
  // refers to finding a placement that minimizes the maximum distance between consecutive "0"s,
  // considering the circular nature.
  // Given only the `isValidPlacement` definition, designing `optimalMaxDistance` predicate
  // to fully capture this "circular" optimization goal directly as a predicate is complex
  // without knowing the expected return value `result`.

  // The problem statement implies `result` should be the *minimum* possible maximum distance.
  // A predicate is generally used to state a property of *one* given placement.
  // Here, `optimalMaxDistance(placement) == result` suggests that `optimalMaxDistance`
  // should return the calculated max distance for that specific placement, and the postcondition
  // then asserts that `result` is minimized across all valid placements.

  // Let's redefine `optimalMaxDistance` as a function that computes the max distance.
  // This seems to align better with `... == result`.
}

function calculateMaxCircularDistance(rooms: string, placement: seq<int>): int
  requires isValidPlacement(rooms, _ -1, placement) // k implicitly derived from |placement| - 1
{
  if |placement| <= 1 then 0 // Or some appropriate base case, if k is > 0 this might not be reached for real
  else
    var max_dist := 0;
    var i := 0;
    while i < |placement| - 1
      invariant 0 <= i < |placement| - 1
      invariant max_dist == (if i == 0 then 0 else max(result for j :: 0 <= j < i :: placement[j+1] - placement[j]))
      decreases |placement| - 1 - i
    {
      var current_dist := placement[i+1] - placement[i];
      if current_dist > max_dist then
        max_dist := current_dist;
      i := i + 1;
    }
    var circular_dist := rooms |> |rooms| - placement[|placement|-1] + placement[0];
    max(max_dist, circular_dist)
}
// The problem asks for `optimalMaxDistance` to be a predicate.
// The phrasing `optimalMaxDistance(placement) == result` strongly suggests it's a function that returns a value.
// If it truly must be a predicate, then it would need to assert that `placement` *is* an optimal one,
// which is extremely difficult to express generally without another value to compare against.

// Assuming `optimalMaxDistance` is intended to be a function that calculates the *maximum* distance for a given placement:
// For the purpose of getting the Dafny code to verify, and given the structure:
// `ensures exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) == result`
// and `result` being an `int`, `optimalMaxDistance` should return an `int`.
// Let's redefine it as a function.

function method OptimalMaxDistanceActual(rooms: string, k: int, placement: seq<int>): int
  requires isValidPlacement(rooms, k, placement)
{
  if k == 0 then 0 // Single placement, no distances
  else
    var current_max_dist := 0;
    var i := 0;
    while i < k
      invariant 0 <= i <= k
      invariant forall j :: 0 <= j < i ==> placement[j+1] - placement[j] <= current_max_dist || j ==0
      invariant (forall j :: 0 <= j < i ==> placement[j+1] - placement[j] <= current_max_dist)
      invariant current_max_dist == CalculateMaxSeqDistance(placement[0..i+1])
      decreases k - i
    {
      var dist := placement[i+1] - placement[i];
      if dist > current_max_dist then
        current_max_dist := dist;
      i := i + 1;
    }
    // Handle the circular wrap-around distance
    var circular_dist := |rooms| - placement[k] + placement[0]; // distance from last '0' to first '0' wrapping around
    max(current_max_dist, circular_dist)
}

function CalculateMaxSeqDistance(s: seq<int>): int
  requires |s| >= 1
{
  if |s| == 1 then 0
  else if |s| == 2 then s[1] - s[0]
  else max(s[1] - s[0], CalculateMaxSeqDistance(s[1..]))
}

// Introduce a helper to find all valid placements. This will not be feasible for large N, but for verification purposes.
// This is not efficient, but helps to reason about existence.
// This function needs to be a method to use `yield`.
// Also, it's not directly needed for the solver part as the solver finds *one* solution.

// The most direct interpretation of the problem and the prompt is that
// `result` should be the smallest possible maximum circular distance.
// We need to implement a search/dynamic programming solution.
// For the given structure (single method, `result` returned), it suggests a direct computation.

// Let's stick with the idea that `optimalMaxDistance` is a function (even though listed as predicate).
// The problem asks for `result` which is an `int`.
// The postcondition `optimalMaxDistance(placement) == result` implies it returns an int.

// Given the `isValidPlacement` predicate, the `optimalMaxDistance` is likely meant to be a function
// that computes the maximum distance for *a given* placement, and the solver should find a `placement`
// that minimizes this value.

// Let's call the function `GetMaxCircularDistance` since `optimalMaxDistance` is defined as a predicate.
// The specification `optimalMaxDistance(placement) == result` could mean that `result` is the value returned by `optimalMaxDistance`,
// and `optimalMaxDistance` is a predicate that is true if the given placement `placement` *is* an optimal one,
// AND its maximum distance is `result`. This seems overly complex.

// Simpler: treat `optimalMaxDistance` as a function method.
function method optimalMaxDistance(rooms: string, placement: seq<int>): int
  requires isValidPlacement(rooms, _ - 1, placement) // k is |placement| - 1
{
  if |placement| <= 1 then 0
  else
    var current_max_dist := 0;
    var i := 0;
    while i < |placement| - 1
      invariant 0 <= i < |placement|
      invariant (forall j :: 0 <= j < i ==> (placement[j+1] - placement[j]) <= current_max_dist)
      invariant current_max_dist == (if i == 0 then 0 else MaxSeqDiff(placement[0..i+1]))
    {
      var dist := placement[i+1] - placement[i];
      if dist > current_max_dist then
        current_max_dist := dist;
      i := i + 1;
    }
    // Circular distance
    var circular_dist := |rooms| - placement[|placement|-1] + placement[0];
    max(current_max_dist, circular_dist)
}

function method MaxSeqDiff(s: seq<int>): int
  requires |s| >= 2
  ensures MaxSeqDiff(s) == max(s[1]-s[0], if |s| > 2 then MaxSeqDiff(s[1..]) else 0)
{
  if |s| == 2 then s[1] - s[0]
  else max(s[1] - s[0], MaxSeqDiff(s[1..]))
}

// To verify solve, we need a method to find the optimal result.
// This typically involves iterating through all possible placements (too many)
// or using binary search on the answer.

// The problem implies a classical "minimax" problem that can often be solved with binary search.
// We can binary search on the `result`.
// For a given `max_allowed_dist`, can we find `k+1` '0's such that the max distance is `max_allowed_dist`?

predicate CanPlace(n: int, k: int, rooms: string, max_allowed_dist: int)
{
  var M := max_allowed_dist; // Alias for brevity

  // We need to pick k+1 '0's.
  // This predicate is essentially checking if a path exists in a graph
  // or a greedy approach works.

  // This predicate is usually a helper for a binary search *approach*, not a direct target.
  // Since `solve` has to return an int, `solve` is responsible for finding this minimized value.
  // The structure `optimalMaxDistance(placement) == result` means `optimalMaxDistance` needs to return `result`.

  // Let's assume the helper is a checker for fixed max_dist `m`.
  // `canPlace(startIndex, count, current_dist_from_prev, m)`
}

// Function to calculate the possible indices of '0's
function GetZeroIndices(rooms: string): seq<int>
  ensures forall i :: 0 <= i < |GetZeroIndices(rooms)| ==> rooms[GetZeroIndices(rooms)[i]] == '0'
  ensures forall i, j :: 0 <= i < j < |GetZeroIndices(rooms)| ==> GetZeroIndices(rooms)[i] < GetZeroIndices(rooms)[j]
{
  var indices: seq<int> := [];
  var i := 0;
  while i < |rooms|
    invariant 0 <= i <= |rooms|
    invariant forall j :: 0 <= j < |indices| ==> rooms[indices[j]] == '0'
    invariant forall j, l :: 0 <= j < l < |indices| ==> indices[j] < indices[l]
    invariant forall j_prime :: 0 <= j_prime < i ==> (rooms[j_prime] == '0' <==> j_prime in indices)
  {
    if rooms[i] == '0' then
      indices := indices + [i];
    i := i + 1;
  }
  indices
}

// A helper for the binary search approach for the feasibility check "Can we achieve max_dist X?"
// This is a standard greedy approach for this type of problem.
lemma {:induction false} MaxInt(a: int, b: int): int
  ensures MaxInt(a, b) == max(a
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, rooms: string) returns (result: int)
    requires n > 0
    requires k > 0 
    requires k < n
    requires |rooms| == n
    requires forall i :: 0 <= i < n ==> rooms[i] == '0' || rooms[i] == '1'
    requires |set i | 0 <= i < n && rooms[i] == '0'| >= k + 1
    ensures result >= 0
    ensures exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) == result
// </vc-spec>
// <vc-code>
predicate optimalMaxDistance(placement: seq<int>)
{
  0 < |placement| &&
  (forall i :: 0 <= i < |placement| -1 ==> placement[i+1] - placement[i] <= placement[0] + (|placement| > 1 ? placement[|placement|-1] - placement[1] : 0))
  // This predicate is tricky. The `optimalMaxDistance`
  // mentioned in the postcondition `ensures exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) == result`
  // refers to finding a placement that minimizes the maximum distance between consecutive "0"s,
  // considering the circular nature.
  // Given only the `isValidPlacement` definition, designing `optimalMaxDistance` predicate
  // to fully capture this "circular" optimization goal directly as a predicate is complex
  // without knowing the expected return value `result`.

  // The problem statement implies `result` should be the *minimum* possible maximum distance.
  // A predicate is generally used to state a property of *one* given placement.
  // Here, `optimalMaxDistance(placement) == result` suggests that `optimalMaxDistance`
  // should return the calculated max distance for that specific placement, and the postcondition
  // then asserts that `result` is minimized across all valid placements.

  // Let's redefine `optimalMaxDistance` as a function that computes the max distance.
  // This seems to align better with `... == result`.
}

function calculateMaxCircularDistance(rooms: string, placement: seq<int>): int
  requires isValidPlacement(rooms, _ -1, placement) // k implicitly derived from |placement| - 1
{
  if |placement| <= 1 then 0 // Or some appropriate base case, if k is > 0 this might not be reached for real
  else
    var max_dist := 0;
    var i := 0;
    while i < |placement| - 1
      invariant 0 <= i < |placement| - 1
      invariant max_dist == (if i == 0 then 0 else max(result for j :: 0 <= j < i :: placement[j+1] - placement[j]))
      decreases |placement| - 1 - i
    {
      var current_dist := placement[i+1] - placement[i];
      if current_dist > max_dist then
        max_dist := current_dist;
      i := i + 1;
    }
    var circular_dist := rooms |> |rooms| - placement[|placement|-1] + placement[0];
    max(max_dist, circular_dist)
}
// The problem asks for `optimalMaxDistance` to be a predicate.
// The phrasing `optimalMaxDistance(placement) == result` strongly suggests it's a function that returns a value.
// If it truly must be a predicate, then it would need to assert that `placement` *is* an optimal one,
// which is extremely difficult to express generally without another value to compare against.

// Assuming `optimalMaxDistance` is intended to be a function that calculates the *maximum* distance for a given placement:
// For the purpose of getting the Dafny code to verify, and given the structure:
// `ensures exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) == result`
// and `result` being an `int`, `optimalMaxDistance` should return an `int`.
// Let's redefine it as a function.

function method OptimalMaxDistanceActual(rooms: string, k: int, placement: seq<int>): int
  requires isValidPlacement(rooms, k, placement)
{
  if k == 0 then 0 // Single placement, no distances
  else
    var current_max_dist := 0;
    var i := 0;
    while i < k
      invariant 0 <= i <= k
      invariant forall j :: 0 <= j < i ==> placement[j+1] - placement[j] <= current_max_dist || j ==0
      invariant (forall j :: 0 <= j < i ==> placement[j+1] - placement[j] <= current_max_dist)
      invariant current_max_dist == CalculateMaxSeqDistance(placement[0..i+1])
      decreases k - i
    {
      var dist := placement[i+1] - placement[i];
      if dist > current_max_dist then
        current_max_dist := dist;
      i := i + 1;
    }
    // Handle the circular wrap-around distance
    var circular_dist := |rooms| - placement[k] + placement[0]; // distance from last '0' to first '0' wrapping around
    max(current_max_dist, circular_dist)
}

function CalculateMaxSeqDistance(s: seq<int>): int
  requires |s| >= 1
{
  if |s| == 1 then 0
  else if |s| == 2 then s[1] - s[0]
  else max(s[1] - s[0], CalculateMaxSeqDistance(s[1..]))
}

// Introduce a helper to find all valid placements. This will not be feasible for large N, but for verification purposes.
// This is not efficient, but helps to reason about existence.
// This function needs to be a method to use `yield`.
// Also, it's not directly needed for the solver part as the solver finds *one* solution.

// The most direct interpretation of the problem and the prompt is that
// `result` should be the smallest possible maximum circular distance.
// We need to implement a search/dynamic programming solution.
// For the given structure (single method, `result` returned), it suggests a direct computation.

// Let's stick with the idea that `optimalMaxDistance` is a function (even though listed as predicate).
// The problem asks for `result` which is an `int`.
// The postcondition `optimalMaxDistance(placement) == result` implies it returns an int.

// Given the `isValidPlacement` predicate, the `optimalMaxDistance` is likely meant to be a function
// that computes the maximum distance for *a given* placement, and the solver should find a `placement`
// that minimizes this value.

// Let's call the function `GetMaxCircularDistance` since `optimalMaxDistance` is defined as a predicate.
// The specification `optimalMaxDistance(placement) == result` could mean that `result` is the value returned by `optimalMaxDistance`,
// and `optimalMaxDistance` is a predicate that is true if the given placement `placement` *is* an optimal one,
// AND its maximum distance is `result`. This seems overly complex.

// Simpler: treat `optimalMaxDistance` as a function method.
function method optimalMaxDistance(rooms: string, placement: seq<int>): int
  requires isValidPlacement(rooms, _ - 1, placement) // k is |placement| - 1
{
  if |placement| <= 1 then 0
  else
    var current_max_dist := 0;
    var i := 0;
    while i < |placement| - 1
      invariant 0 <= i < |placement|
      invariant (forall j :: 0 <= j < i ==> (placement[j+1] - placement[j]) <= current_max_dist)
      invariant current_max_dist == (if i == 0 then 0 else MaxSeqDiff(placement[0..i+1]))
    {
      var dist := placement[i+1] - placement[i];
      if dist > current_max_dist then
        current_max_dist := dist;
      i := i + 1;
    }
    // Circular distance
    var circular_dist := |rooms| - placement[|placement|-1] + placement[0];
    max(current_max_dist, circular_dist)
}

function method MaxSeqDiff(s: seq<int>): int
  requires |s| >= 2
  ensures MaxSeqDiff(s) == max(s[1]-s[0], if |s| > 2 then MaxSeqDiff(s[1..]) else 0)
{
  if |s| == 2 then s[1] - s[0]
  else max(s[1] - s[0], MaxSeqDiff(s[1..]))
}

// To verify solve, we need a method to find the optimal result.
// This typically involves iterating through all possible placements (too many)
// or using binary search on the answer.

// The problem implies a classical "minimax" problem that can often be solved with binary search.
// We can binary search on the `result`.
// For a given `max_allowed_dist`, can we find `k+1` '0's such that the max distance is `max_allowed_dist`?

predicate CanPlace(n: int, k: int, rooms: string, max_allowed_dist: int)
{
  var M := max_allowed_dist; // Alias for brevity

  // We need to pick k+1 '0's.
  // This predicate is essentially checking if a path exists in a graph
  // or a greedy approach works.

  // This predicate is usually a helper for a binary search *approach*, not a direct target.
  // Since `solve` has to return an int, `solve` is responsible for finding this minimized value.
  // The structure `optimalMaxDistance(placement) == result` means `optimalMaxDistance` needs to return `result`.

  // Let's assume the helper is a checker for fixed max_dist `m`.
  // `canPlace(startIndex, count, current_dist_from_prev, m)`
}

// Function to calculate the possible indices of '0's
function GetZeroIndices(rooms: string): seq<int>
  ensures forall i :: 0 <= i < |GetZeroIndices(rooms)| ==> rooms[GetZeroIndices(rooms)[i]] == '0'
  ensures forall i, j :: 0 <= i < j < |GetZeroIndices(rooms)| ==> GetZeroIndices(rooms)[i] < GetZeroIndices(rooms)[j]
{
  var indices: seq<int> := [];
  var i := 0;
  while i < |rooms|
    invariant 0 <= i <= |rooms|
    invariant forall j :: 0 <= j < |indices| ==> rooms[indices[j]] == '0'
    invariant forall j, l :: 0 <= j < l < |indices| ==> indices[j] < indices[l]
    invariant forall j_prime :: 0 <= j_prime < i ==> (rooms[j_prime] == '0' <==> j_prime in indices)
  {
    if rooms[i] == '0' then
      indices := indices + [i];
    i := i + 1;
  }
  indices
}

// A helper for the binary search approach for the feasibility check "Can we achieve max_dist X?"
// This is a standard greedy approach for this type of problem.
lemma {:induction false} MaxInt(a: int, b: int): int
  ensures MaxInt(a, b) == max(a
// </vc-code>

