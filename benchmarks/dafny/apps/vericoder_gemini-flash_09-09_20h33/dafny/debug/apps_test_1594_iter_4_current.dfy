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
  requires 0 <= low <= high + 1 <= |songs| + 1
  requires query_val > 0
  requires forall i :: 0 <= i < |songs| ==> songs[i].0 > 0 && songs[i].1 > 0
  requires high >= 1 ==> cumulative_duration_at_song(songs, high - 1) >= query_val || high == |songs| + 1
  requires low <= |songs| ==> cumulative_duration_at_song(songs, low - 1) < query_val || low == 1
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
    if mid == 0 then // added to handle mid=0 case explicitly
      find_song_index(songs, query_val, low, mid)
    else if query_val <= cumulative_duration_at_song(songs, mid - 1) then
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
  {
    var low_bound := 1;
    if i > 0 {
      assert result[i-1] >= 1; // From loop invariant
      if queries[i] > cumulative_duration_at_song(songs, result[i-1] - 1) {
        low_bound := result[i-1];
      } else if queries[i] > queries[i-1] {
        low_bound := result[i-1];
      } else {
        low_bound := 1;
      }
    }
    
    var final_low_bound := low_bound;
    if i > 0 {
        if queries[i] > cumulative_duration_at_song(songs, result[i-1]-1) {
           final_low_bound := result[i-1];
        } else if queries[i] > queries[i-1] {
           final_low_bound := result[i-1];
        }
    }
    
    assert final_low_bound >= 1;
    // The upper bound for final_low_bound should be n, as result[i-1] could be n and low_bound could be 1
    // The condition for find_song_index is 0 <= low <= high + 1 <= |songs| + 1. Here high is n.
    // So final_low_bound <= n is needed.
    assert final_low_bound <= n; 

    var found_idx := find_song_index(songs, queries[i], final_low_bound, n);
    result[i] := found_idx;
  }
  return result;
}
// </vc-code>

