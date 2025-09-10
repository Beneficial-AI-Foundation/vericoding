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
  requires high >= 1 ==> query_val <= cumulative_duration_at_song(songs, high - 1)
  requires low >= 1 ==> query_val > cumulative_duration_at_song(songs, low - 2) || low == 1
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
  if m == 0 { return result; }

  assert forall i :: 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0;
  assert cumulative_duration_at_song(songs, n - 1) == sum_playlist_duration(songs, n);

  for i := 0 to m - 1
    invariant 0 <= i <= m
    invariant |result[..i]| == i
    invariant forall k :: 0 <= k < i ==> 1 <= result[k] <= n
    invariant forall k :: 0 <= k < i ==> queries[k] <= cumulative_duration_at_song(songs, result[k] - 1)
    invariant forall k :: 0 <= k < i ==> result[k] == 1 || queries[k] > cumulative_duration_at_song(songs, result[k] - 2)
    invariant i == 0 || result[i-1] <= n
    invariant n >= 0
    invariant m >= 0
    invariant |songs| == n
    invariant |queries| == m
    invariant forall k :: 0 <= k < n ==> songs[k].0 > 0 && songs[k].1 > 0
    invariant forall k :: 0 <= k < m - 1 ==> queries[k] < queries[k + 1]
    invariant forall k :: 0 <= k < m ==> queries[k] >= 1
    invariant m == 0 || queries[m-1] <= sum_playlist_duration(songs, n)
    invariant i == 0 || queries[i-1] <= queries[i] // This is true because queries are sorted.
  {
    var low_bound := 1;
    if i > 0 {
      assert result[i-1] >= 1; // From loop invariant
      if queries[i] > cumulative_duration_at_song(songs, result[i-1] - 1) then
        low_bound := result[i-1];
      else if queries[i] > queries[i-1] then
        // If queries[i] <= cumulative_duration_at_song(songs, result[i-1] - 1)
        // AND queries[i] > queries[i-1]
        // AND queries[i-1] > cumulative_duration_at_song(songs, result[i-1] - 2)
        // Then we know that result[i] cannot be less than result[i-1],
        // because that would imply queries[i] <= cumulative_duration_at_song(songs, result[i-1] - 2),
        // which contradicts queries[i] > queries[i-1].
        // So we can still start from result[i-1].
        low_bound := result[i-1];
      else
        // If queries[i] == queries[i-1], which is not allowed by the spec.
        // Or if queries[i] < queries[i-1], which is not allowed by the spec.
        // Given queries are strictly increasing, this else branch implies queries[i] <= queries[i-1]
        // (which is queries[i] < queries[i-1] from the spec), and queries[i] <= cum_duration_at_song(songs, result[i-1]-1)
        // In this case, we search from 1.
        low_bound := 1;
    }
    
    var final_low_bound := low_bound;
    if i > 0 && queries[i] >= queries[i-1] && result[i-1] > 0 {
        if queries[i] > cumulative_duration_at_song(songs, result[i-1]-1) {
            final_low_bound := result[i-1];
        } else if queries[i] > queries[i-1] {
            final_low_bound := result[i-1];
        }
    }
    
    assert final_low_bound >= 1;
    assert final_low_bound <= n; // Since result[i-1] <= n and low_bound is either 1 or result[i-1]

    var found_idx := find_song_index(songs, queries[i], final_low_bound, n);
    result[i] := found_idx;
  }
  return result;
}
// </vc-code>

