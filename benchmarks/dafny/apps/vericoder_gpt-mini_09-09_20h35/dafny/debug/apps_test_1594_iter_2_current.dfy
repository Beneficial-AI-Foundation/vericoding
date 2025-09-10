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
lemma queries_le_last(queries: seq<int>, m: int, i: int)
  requires 0 <= i < m
  requires forall k :: 0 <= k < m - 1 ==> queries[k] < queries[k + 1]
  decreases m - i
  ensures queries[i] <= queries[m-1]
{
  if i == m - 1 {
    assert queries[i] <= queries[m-1];
    return;
  }
  // queries[i] < queries[i+1]
  assert queries[i] < queries[i+1];
  queries_le_last(queries, m, i + 1);
  // By induction queries[i+1] <= queries[m-1], and queries[i] < queries[i+1], so queries[i] <= queries[m-1]
  assert queries[i+1] <= queries[m-1];
  assert queries[i] < queries[i+1];
  assert queries[i] <= queries[m-1];
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
  var resArr := new int[m];
  var curSong := 0;
  var curCum := 0;
  var i := 0;
  assert curCum == cumulative_duration_at_song(songs, curSong - 1);
  while i < m
    invariant 0 <= i <= m
    invariant 0 <= curSong <= n
    invariant curCum == cumulative_duration_at_song(songs, curSong - 1)
    invariant forall t :: 0 <= t < i ==> 1 <= resArr[t] <= n &&
                                      queries[t] <= cumulative_duration_at_song(songs, resArr[t] - 1) &&
                                      (resArr[t] == 1 || queries[t] > cumulative_duration_at_song(songs, resArr[t] - 2))
    decreases m - i
  {
    var q := queries[i];
    // q <= total sum of playlist, proved using monotonicity of queries and the precondition on queries[m-1]
    if m > 0 {
      queries_le_last(queries, m, i);
      assert queries[i] <= queries[m - 1];
      assert queries[m - 1] <= sum_playlist_duration(songs, n);
      assert q <= sum_playlist_duration(songs, n);
    }

    while curSong < n && curCum + songs[curSong].0 * songs[curSong].1 < q
      invariant 0 <= curSong <= n
      invariant curCum == cumulative_duration_at_song(songs, curSong - 1)
      decreases n - curSong
    {
      assert curSong < n;
      // by definition of cumulative_duration_at_song
      assert cumulative_duration_at_song(songs, curSong) == curCum + songs[curSong].0 * songs[curSong].1;
      curCum := curCum + songs[curSong].0 * songs[curSong].1;
      curSong := curSong + 1;
    }
    // After the inner loop, curSong < n must hold because q <= total duration
    assert curSong < n;
    resArr[i] := curSong + 1;
    i := i + 1;
  }
  result := resArr[..];
}
// </vc-code>

