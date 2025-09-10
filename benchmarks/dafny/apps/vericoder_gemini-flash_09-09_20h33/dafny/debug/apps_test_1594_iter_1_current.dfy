function sum_playlist_duration(songs: seq<(int, int)>, n: int): int
  requires n >= 0
  requires |songs| >= n
  requires forall i :: 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0
{
  if n == 0 then 0
  else songs[n-1].0 * songs[n-1].1 + sum_playlist_duration(songs, n-1)
}

function cumulative_duration_at_song(songs: seq<(int, int)>, song_idx: int): int
  requires song_idx >= -1
  requires |songs| > song_idx
  requires forall i :: 0 <= i <= song_idx ==> songs[i].0 > 0 && songs[i].1 > 0
{
  if song_idx == -1 then 0
  else songs[song_idx].0 * songs[song_idx].1 + cumulative_duration_at_song(songs, song_idx - 1)
}

// <vc-helpers>
function find_song_index(songs: seq<(int, int)>, query_val: int, low: int, high: int): int
  requires 0 <= low <= high < |songs| + 1
  requires query_val > 0
  requires forall i :: 0 <= i < |songs| ==> songs[i].0 > 0 && songs[i].1 > 0
  requires query_val <= cumulative_duration_at_song(songs, high - 1)
  decreases high - low
  ensures 1 <= find_song_index(songs, query_val, low, high) <= high
  ensures query_val <= cumulative_duration_at_song(songs, find_song_index(songs, query_val, low, high) - 1)
  ensures find_song_index(songs, query_val, low, high) == 1 || query_val > cumulative_duration_at_song(songs, find_song_index(songs, query_val, low, high) - 2)
{
  if low == high then
    high
  else if low + 1 == high then
    if query_val <= cumulative_duration_at_song(songs, low - 1) then low
    else high
  else
    var mid := low + (high - low) / 2;
    if query_val <= cumulative_duration_at_song(songs, mid - 1) then
      find_song_index(songs, query_val, low, mid)
    else
      find_song_index(songs, query_val, mid + 1, high)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, songs: seq<(int, int)>, queries: seq<int>) returns (result: seq<int>)
  requires n >= 0
  requires m >= 0
  requires |songs| == n
  requires |queries| == m
  requires forall i :: 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0
  requires forall i :: 0 <= i < m - 1 ==> queries[i] < queries[i + 1]
  requires forall i :: 0 <= i < m ==> queries[i] >= 1
  requires m == 0 || queries[m-1] <= sum_playlist_duration(songs, n)
  ensures |result| == m
  ensures forall i :: 0 <= i < m ==> 1 <= result[i] <= n
  ensures forall i :: 0 <= i < m ==> queries[i] <= cumulative_duration_at_song(songs, result[i] - 1)
  ensures forall i :: 0 <= i < m ==> result[i] == 1 || queries[i] > cumulative_duration_at_song(songs, result[i] - 2)
// </vc-spec>
// <vc-code>
{
  var result := new int[m];
  if m == 0 then return result;

  var current_high := n; // Represents the upper bound for binary search, initially n
  var last_found_idx := 0; // The index of the song found for the previous query

  assert forall i :: 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0;
  assert cumulative_duration_at_song(songs, n - 1) == sum_playlist_duration(songs, n);

  for i := 0 to m - 1
    invariant 0 <= i <= m
    invariant |result[..i]| == i
    invariant forall k :: 0 <= k < i ==> 1 <= result[k] <= n
    invariant forall k :: 0 <= k < i ==> queries[k] <= cumulative_duration_at_song(songs, result[k] - 1)
    invariant forall k :: 0 <= k < i ==> result[k] == 1 || queries[k] > cumulative_duration_at_song(songs, result[k] - 2)
    invariant i == 0 || last_found_idx == result[i-1]
    invariant 0 <= current_high <= n
    invariant queries[m-1] <= cumulative_duration_at_song(songs, n - 1)
    invariant i == 0 || queries[i-1] <= queries[i] // This isn't quite right for the loop inv
    invariant forall k :: i <= k < m - 1 ==> queries[k] < queries[k+1] // ensures queries are sorted for remaining queries
  {
    var low_bound := 1;
    if i > 0 && queries[i] > cumulative_duration_at_song(songs, result[i-1] - 1) then
      // If the current query is greater than the cumulative duration up to the previous found song,
      // we can start the search from the previously found song's index.
      low_bound := result[i-1];
    else if i > 0 then
      // If current query is <= cumulative_duration_at_song(songs,result[i-1] - 1),
      // the answer might be result[i-1] or even earlier.
      // But since queries are strictly increasing (queries[i-1] < queries[i]),
      // and we are looking for the *first* song that satisfies the condition,
      // the answer must be at least result[i-1] if queries[i-1] was found at result[i-1].
      // So, if queries[i] > queries[i-1], the new song index must be >= result[i-1].
      // Consider queries: [5, 10], songs: [(2,2), (3,3), (4,4)] -> cumulative: [4, 13, 29]
      // For query 5, result is 2 (song_idx 1).
      // For query 10, start search for song from index 2.
      low_bound := result[i-1];

    if low_bound < 1 then low_bound := 1; // Sanity check

    var found_idx := find_song_index(songs, queries[i], low_bound, n);
    result[i] := found_idx;
    last_found_idx := found_idx;
  }
  return result;
}
// </vc-code>

