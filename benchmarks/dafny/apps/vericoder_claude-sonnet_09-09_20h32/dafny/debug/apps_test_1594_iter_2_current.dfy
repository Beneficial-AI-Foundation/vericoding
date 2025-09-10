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
function max(a: int, b: int): int
{
  if a >= b then a else b
}

lemma cumulative_duration_monotonic(songs: seq<(int, int)>, i: int, j: int)
  requires i >= -1 && j >= -1
  requires |songs| > i && |songs| > j
  requires forall k :: 0 <= k <= max(i, j) ==> songs[k].0 > 0 && songs[k].1 > 0
  requires i <= j
  ensures cumulative_duration_at_song(songs, i) <= cumulative_duration_at_song(songs, j)
{
  if i == j {
  } else if i == -1 {
    cumulative_duration_positive(songs, j);
  } else {
    cumulative_duration_monotonic(songs, i, j-1);
  }
}

lemma cumulative_duration_positive(songs: seq<(int, int)>, song_idx: int)
  requires song_idx >= 0
  requires |songs| > song_idx
  requires forall i :: 0 <= i <= song_idx ==> songs[i].0 > 0 && songs[i].1 > 0
  ensures cumulative_duration_at_song(songs, song_idx) > 0
{
  if song_idx == 0 {
  } else {
    cumulative_duration_positive(songs, song_idx - 1);
  }
}

lemma sum_playlist_equals_cumulative(songs: seq<(int, int)>, n: int)
  requires n >= 0
  requires |songs| >= n
  requires forall i :: 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0
  ensures sum_playlist_duration(songs, n) == if n == 0 then 0 else cumulative_duration_at_song(songs, n-1)
{
  if n == 0 {
  } else {
    sum_playlist_equals_cumulative(songs, n-1);
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
  var query_idx := 0;
  
  while query_idx < m
    invariant 0 <= query_idx <= m
    invariant |result| == query_idx
    invariant forall i :: 0 <= i < query_idx ==> 1 <= result[i] <= n
    invariant forall i :: 0 <= i < query_idx ==> queries[i] <= cumulative_duration_at_song(songs, result[i] - 1)
    invariant forall i :: 0 <= i < query_idx ==> result[i] == 1 || queries[i] > cumulative_duration_at_song(songs, result[i] - 2)
  {
    var song_idx := 0;
    
    while song_idx < n && queries[query_idx] > cumulative_duration_at_song(songs, song_idx)
      invariant 0 <= song_idx <= n
      invariant forall j :: 0 <= j < song_idx ==> queries[query_idx] > cumulative_duration_at_song(songs, j)
    {
      cumulative_duration_monotonic(songs, song_idx, song_idx);
      song_idx := song_idx + 1;
    }
    
    if song_idx < n {
      cumulative_duration_monotonic(songs, if song_idx == 0 then -1 else song_idx - 1, song_idx);
      result := result + [song_idx + 1];
    } else {
      sum_playlist_equals_cumulative(songs, n);
      result := result + [n];
    }
    
    query_idx := query_idx + 1;
  }
}
// </vc-code>

