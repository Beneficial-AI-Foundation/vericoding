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
lemma cumulative_duration_monotonic(songs: seq<(int, int)>, i: int, j: int)
  requires -1 <= i < j < |songs|
  requires forall k :: 0 <= k <= j ==> songs[k].0 > 0 && songs[k].1 > 0
  ensures cumulative_duration_at_song(songs, i) < cumulative_duration_at_song(songs, j)
{
  if i == -1 {
    assert cumulative_duration_at_song(songs, i) == 0;
    assert cumulative_duration_at_song(songs, j) >= songs[j].0 * songs[j].1 > 0;
  } else if i == j - 1 {
    assert cumulative_duration_at_song(songs, j) == songs[j].0 * songs[j].1 + cumulative_duration_at_song(songs, i);
    assert songs[j].0 * songs[j].1 > 0;
  } else {
    cumulative_duration_monotonic(songs, i, j - 1);
  }
}

lemma sum_equals_cumulative(songs: seq<(int, int)>, n: int)
  requires n >= 0
  requires |songs| >= n
  requires forall i :: 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0
  ensures sum_playlist_duration(songs, n) == cumulative_duration_at_song(songs, n - 1)
{
  if n == 0 {
    assert sum_playlist_duration(songs, n) == 0;
    assert cumulative_duration_at_song(songs, n - 1) == 0;
  } else {
    assert sum_playlist_duration(songs, n) == songs[n-1].0 * songs[n-1].1 + sum_playlist_duration(songs, n-1);
    sum_equals_cumulative(songs, n - 1);
    if n == 1 {
      assert cumulative_duration_at_song(songs, n - 1) == songs[0].0 * songs[0].1;
    } else {
      assert cumulative_duration_at_song(songs, n - 1) == songs[n-1].0 * songs[n-1].1 + cumulative_duration_at_song(songs, n - 2);
    }
  }
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
  var song_idx := 0;
  var cumulative_time := 0;
  
  for query_idx := 0 to m
    invariant 0 <= song_idx <= n
    invariant |result| == query_idx
    invariant song_idx == 0 ==> cumulative_time == 0
    invariant song_idx > 0 ==> cumulative_time == cumulative_duration_at_song(songs, song_idx - 1)
    invariant forall i :: 0 <= i < query_idx ==> 1 <= result[i] <= n
    invariant forall i :: 0 <= i < query_idx ==> queries[i] <= cumulative_duration_at_song(songs, result[i] - 1)
    invariant forall i :: 0 <= i < query_idx ==> result[i] == 1 || queries[i] > cumulative_duration_at_song(songs, result[i] - 2)
    invariant query_idx > 0 ==> song_idx >= result[query_idx - 1]
    invariant query_idx > 0 ==> cumulative_time >= cumulative_duration_at_song(songs, result
// </vc-code>

