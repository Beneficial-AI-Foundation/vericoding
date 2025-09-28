// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): This iteration refines the binary search logic in `find_song_index`. The critical change is in the `else` branch of the binary search. Previously, if `target_duration <= cumulative_duration_at_song(songs, mid)` was false, `high` was consistently set to `mid`. However, in cases where `low == mid`, this could lead to an infinite loop if the `low` bound was not updated. The updated code now correctly sets `low := mid + 1` when the target duration is greater than the cumulative duration at `mid`. This ensures that the search space always shrinks appropriately, maintaining the correctness of the binary search algorithm. Additionally, the `mid` calculation is now performed as `low + (high - low) / 2` to avoid potential overflow compared to `(low + high) / 2`. */
function find_song_index(songs: seq<(int, int)>, target_duration: int, low: int, high: int): int
  requires 0 <= low <= high < |songs|
  requires target_duration > 0
  requires cumulative_duration_at_song(songs, low-1) < target_duration <= cumulative_duration_at_song(songs, high)
  ensures low <= find_song_index(songs, target_duration, low, high) <= high
  ensures target_duration <= cumulative_duration_at_song(songs, find_song_index(songs, target_duration, low, high))
  ensures find_song_index(songs, target_duration, low, high) == 0 || target_duration > cumulative_duration_at_song(songs, find_song_index(songs, target_duration, low, high) - 1)
{
  if low == high then
    low
  else
    var mid := low + (high - low) / 2;
    if target_duration <= cumulative_duration_at_song(songs, mid) then
      find_song_index(songs, target_duration, low, mid)
    else
      find_song_index(songs, target_duration, mid + 1, high)
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
/* code modified by LLM (iteration 5): Fixed compilation error: `new` can only be applied to class types. Changed `new seq<int>(m, _ => 0)` to `seq<int>(m, _ => 0)` for sequence initialization. */
{
  var results: seq<int> := seq<int>(m, _ => 0);

  if m == 0 {
    return results;
  }

  var current_query_idx := 0;

  while current_query_idx < m
    invariant 0 <= current_query_idx <= m
    invariant forall i :: 0 <= i < current_query_idx ==> 1 <= results[i] <= n
    invariant forall i :: 0 <= i < current_query_idx ==> queries[i] <= cumulative_duration_at_song(songs, results[i] - 1)
    invariant forall i :: 0 <= i < current_query_idx ==> results[i] == 1 || queries[i] > cumulative_duration_at_song(songs, results[i] - 2)
    invariant n == 0 || (current_query_idx == 0 || (queries[current_query_idx-1] <= cumulative_duration_at_song(songs, results[current_query_idx-1]-1)))
  {
    var target_duration := queries[current_query_idx];

    var search_low: int;
    if current_query_idx == 0 {
      search_low := 0;
    } else {
      search_low := results[current_query_idx - 1] - 1;
    }

    var current_song_idx: int;

    current_song_idx := find_song_index(songs, target_duration, search_low, n - 1);
    results := results[current_query_idx := current_song_idx + 1];
    current_query_idx := current_query_idx + 1;
  }

  return results;
}
// </vc-code>
