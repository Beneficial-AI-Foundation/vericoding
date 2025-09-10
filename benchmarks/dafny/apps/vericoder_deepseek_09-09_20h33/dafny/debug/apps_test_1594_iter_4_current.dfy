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
lemma cumulative_duration_at_song_monotonic(songs: seq<(int, int)>, i: int, j: int)
  requires |songs| > 0
  requires forall k :: 0 <= k < |songs| ==> songs[k].0 > 0 && songs[k].1 > 0
  requires -1 <= i <= j < |songs|
  ensures cumulative_duration_at_song(songs, i) <= cumulative_duration_at_song(songs, j)
{
  if i < j {
    cumulative_duration_at_song_monotonic(songs, i + 1, j);
    assert cumulative_duration_at_song(songs, i) <= cumulative_duration_at_song(songs, i + 1);
  }
}

lemma cumulative_duration_positive_step(songs: seq<(int, int)>, idx: int)
  requires |songs| > 0
  requires forall k :: 0 <= k < |songs| ==> songs[k].0 > 0 && songs[k].1 > 0
  requires 0 <= idx < |songs|
  ensures cumulative_duration_at_song(songs, idx - 1) < cumulative_duration_at_song(songs, idx)
{
  // The duration at idx is strictly greater than at idx-1 because songs[idx].0 * songs[idx].1 > 0
}

lemma cumulative_duration_bound(songs: seq<(int, int)>, idx: int, query: int)
  requires |songs| > 0
  requires forall k :: 0 <= k < |songs| ==> songs[k].0 > 0 && songs[k].1 > 0
  requires 0 <= idx < |songs|
  requires cumulative_duration_at_song(songs, idx - 1) < query <= cumulative_duration_at_song(songs, idx)
  ensures query <= cumulative_duration_at_song(songs, idx)
  ensures idx == 0 || query > cumulative_duration_at_song(songs, idx - 1)
{
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
  result := [];
  var current_total := 0;
  var song_idx := 0;
  var query_idx := 0;
  
  while query_idx < |queries|
    invariant 0 <= song_idx <= n
    invariant 0 <= query_idx <= |queries|
    invariant |result| == query_idx
    invariant current_total == cumulative_duration_at_song(songs, song_idx - 1)
    invariant forall i :: 0 <= i < query_idx ==> 1 <= result[i] <= n
    invariant forall i :: 0 <= i < query_idx ==> queries[i] <= cumulative_duration_at_song(songs, result[i] - 1)
    invariant forall i :: 0 <= i < query_idx ==> result[i] == 1 || queries[i] > cumulative_duration_at_song(songs, result[i] - 2)
    decreases |queries| - query_idx
  {
    while song_idx < n && current_total + songs[song_idx].0 * songs[song_idx].1 < queries[query_idx]
      invariant 0 <= song_idx <= n
      invariant current_total == cumulative_duration_at_song(songs, song_idx - 1)
      decreases n - song_idx
    {
      current_total := current_total + songs[song_idx].0 * songs[song_idx].1;
      song_idx := song_idx + 1;
    }
    
    var answer := song_idx + 1;
    if song_idx == n {
      answer := n;
    }
    result := result + [answer];
    query_idx := query_idx + 1;
  }
}
// </vc-code>

