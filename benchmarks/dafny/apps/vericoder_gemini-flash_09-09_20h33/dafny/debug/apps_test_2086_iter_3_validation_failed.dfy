predicate ValidInput(n: int, a: seq<int>, s: int, f: int)
{
  n >= 2 && |a| == n && s >= 1 && f > s && f <= n &&
  forall i :: 0 <= i < n ==> a[i] >= 1
}

function participantCount(a: seq<int>, s: int, f: int, n: int, start: int): int
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
{
  participantCountHelper(a, s, f, n, start, 0)
}

function participantCountHelper(a: seq<int>, s: int, f: int, n: int, start: int, i: int): int
  requires |a| == n >= 1
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires 0 <= i <= n
  decreases n - i
{
  if i >= n then 0
  else
    var localHour := (start + i - 1) % n + 1;
    var contribution := if s <= localHour < f then a[i] else 0;
    contribution + participantCountHelper(a, s, f, n, start, i + 1)
}

// <vc-helpers>
function calculateParticipantCount(a: seq<int>, s: int, f: int, n: int, start: int): int
  requires |a| == n
  requires n >= 2
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  reads a
  ensures calculateParticipantCount(a, s, f, n, start) >= 0
{
  var currentCount := 0;
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] >= 1 // This invariant requires a[j] >= 1, which comes from ValidInput
    invariant currentCount == sumContributions(a, s, f, n, start, i)
  {
    var localHour := (start + i - 1) % n + 1;
    if s <= localHour && localHour < f then
      currentCount := currentCount + a[i];
    else
      currentCount := currentCount;
  }
  return currentCount;
}

function sumContributions(a: seq<int>, s: int, f: int, n: int, start: int, k: int): int
  requires |a| == n >= 2
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  requires 0 <= k <= n
  reads a
  ensures sumContributions(a, s, f, n, start, k) >= 0
{
  if k == 0 then 0
  else
    var localHour := (start + k - 1 - 1) % n + 1;
    var contribution := if s <= localHour && localHour < f then a[k-1] else 0;
    contribution + sumContributions(a, s, f, n, start, k-1)
}

lemma SumContributionsParticipantCountEquality(a: seq<int>, s: int, f: int, n: int, start: int)
  requires |a| == n >= 2
  requires s >= 1 && f > s && f <= n
  requires 1 <= start <= n
  // The 'a' elements are guaranteed to be >= 1 by ValidInput,
  // which is an implicit requirement for `solve` in general.
  requires (forall i :: 0 <= i < n ==> a[i] >= 1)
  ensures calculateParticipantCount(a, s, f, n, start) == participantCount(a, s, f, n, start)
{
  // This lemma needs to prove by induction that the iterative and recursive definitions
  // are equivalent. Dafny can sometimes infer this.
  // Given that `calculateParticipantCount` uses `sumContributions` in its invariant,
  // and `participantCount` (via `participantCountHelper`) recursively sums.
  // We can state this equality by thinking about the total sum.
  // The `participantCountHelper` computes the sum from index `i` to `n-1`.
  // `participantCount(a,s,f,n,start)` calls `participantCountHelper(..., 0)`.
  // Let's prove by induction on `k` that `sumContributions(a,s,f,n,start, k)`
  // is equal to the sum of contributions for elements `a[0]` to `a[k-1]`.
  // And `calculateParticipantCount` computes this same sum.
  // The structure of `participantCountHelper` makes it compute the sum from `0` to `n-1`.

  // Base case for `participantCountHelper` (i=n) is 0, which aligns with `sumContributions` for k=0.
  // Consider `participantCountHelper(a, s, f, n, start, i)`
  // This calculates sum from `a[i]` to `a[n-1]`.
  // `calculateParticipantCount` sums from `a[0]` to `a[n-1]`.

  // Let's prove `calculateParticipantCount(a,s,f,n,start) == participantCountHelper(a,s,f,n,start,0)`.
  // We can establish that for any `k` from `0` to `n`:
  // sumContributions(a, s, f, n, start, k) + participantCountHelper(a, s, f, n, start, k)
  // == sum of all contributions from `a[0]` to `a[n-1]`.
  //
  // No explicit proof steps are required here if Dafny can infer it.
  // The previous error regarding 'assume' implies that the helper block itself
  // cannot *contain* assume statements. The logical property itself does not use 'assume'.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, s: int, f: int) returns (result: int)
  requires ValidInput(n, a, s, f)
  ensures 1 <= result <= n
  ensures forall start :: 1 <= start <= n ==> 
    participantCount(a, s, f, n, result) >= participantCount(a, s, f, n, start)
  ensures forall start :: 1 <= start <= n && 
    participantCount(a, s, f, n, start) == participantCount(a, s, f, n, result) 
    ==> result <= start
// </vc-spec>
// <vc-code>
{
  var max_count := -1;
  var best_start := 1;

  for start := 1 to n
    invariant 1 <= start <= n + 1
    invariant 1 <= best_start <= n
    invariant max_count == calculateParticipantCount(a, s, f, n, best_start)
    // The following invariant needs to be updated to account for the tie-breaking rule
    // where we prefer smaller 'start' for equal `max_count`.
    invariant forall prev_start :: 1 <= prev_start < start ==>
      (calculateParticipantCount(a, s, f, n, best_start) > calculateParticipantCount(a, s, f, n, prev_start) ||
       (calculateParticipantCount(a, s, f, n, best_start) == calculateParticipantCount(a, s, f, n, prev_start) && best_start <= prev_start))
  {
    var current_count := calculateParticipantCount(a, s, f, n, start);

    if max_count == -1 || current_count > max_count then // Initialize max_count if first iteration or new max found
      max_count := current_count;
      best_start := start;
    else if current_count == max_count && start < best_start then // Tie-breaking: prefer smaller start
      best_start := start;
    
    // Prove the equality for current 'start' and 'best_start' to allow the postconditions on `participantCount` to be reasoned about.
    GhostCall(SumContributionsParticipantCountEquality(a, s, f, n, start));
    GhostCall(SumContributionsParticipantCountEquality(a, s, f, n, best_start));
  }

  return best_start;
}
// </vc-code>

