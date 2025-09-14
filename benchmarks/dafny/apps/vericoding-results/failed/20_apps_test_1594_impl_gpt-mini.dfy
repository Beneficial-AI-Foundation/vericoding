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
  requires m >= 1
  requires forall k :: 0 <= k < m - 1 ==> queries[k] < queries[k + 1]
  decreases m - i
  ensures queries[i] <= queries[m-1]
{
  if i == m - 1 {
    assert queries[i] <= queries[m-1];
    return;
  }
  // i < m-1, so i+1 and m-1 are in range
  assert queries[i] < queries[i+1];
  queries_le_last(queries, m, i + 1);
  assert queries[i+1] <= queries[m-1];
  assert queries[i] < queries[i+1];
  assert queries[i] <= queries[m-1];
}

lemma cum_equals_sum(songs: seq<(int, int)>, k: int)
  requires k >= 1
  requires |songs| >= k
  requires forall i :: 0 <= i < k ==> songs[i].0 > 0 && songs[i].1 > 0
  ensures cumulative_duration_at_song(songs, k - 1) == sum_playlist_duration(songs, k)
{
  if k == 1 {
    // cumulative_duration_at_song(songs, 0) == songs[0].0 * songs[0].1
    assert cumulative_duration_at_song(songs, 0) == songs[0].0 * songs[0].1 + cumulative_duration_at_song(songs, -1);
    assert cumulative_duration_at_song(songs, -1) == 0;
    assert cumulative_duration_at_song(songs, 0) == songs[0].0 * songs[0].1;
    // sum_playlist_duration(songs,1) == songs[0].0 * songs[0].1
    assert sum_playlist_duration(songs, 1) == songs[0].0 * songs[0].1;
  } else {
    // use induction on k
    cum_equals_sum(songs, k - 1);
    // expand definitions
    assert cumulative_duration_at_song(songs, k - 1) == cumulative_duration_at_song(songs, k - 2) + songs[k - 1].0 * songs[k - 1].1;
    assert sum_playlist_duration(songs, k) == sum_playlist_duration(songs, k - 1) + songs[k - 1].0 * songs[k - 1].1;
    // by induction cumulative_duration_at_song(songs, k-2) == sum_playlist_duration(songs, k-1)
    assert cumulative_duration_at_song(songs, k - 2) == sum_playlist_duration(songs, k - 1);
  }
  // conclude equality (Dafny will use the above facts)
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
    invariant (forall t :: 0 <= t < i ==> (1 <= resArr[t] <= n &&
                                           queries[t] <= cumulative_duration_at_song(songs, resArr[t] - 1) &&
                                           (resArr[t] == 1 || queries[t] > cumulative_duration_at_song(songs, resArr[t] - 2))))
    invariant i < m ==> curCum < queries[i]
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

    // curCum < q follows from the loop invariant i < m ==> curCum < queries[i]
    assert curCum < q;

    while curSong < n && curCum + songs[curSong].0 * songs[curSong].1 < q
      invariant 0 <= curSong <= n
      invariant curCum == cumulative_duration_at_song(songs, curSong - 1)
      invariant i < m ==> curCum < q
      decreases n - curSong
    {
      assert curSong < n;
      // by definition of cumulative_duration_at_song
      assert cumulative_duration_at_song(songs, curSong) == curCum + songs[curSong].0 * songs[curSong].1;
      curCum := curCum + songs[curSong].0 * songs[curSong].1;
      curSong := curSong + 1;
      // after increment, still curCum < q holds because loop condition ensured previous curCum + duration < q
      assert curCum < q;
    }
    // After the inner loop, curSong < n must hold because q <= total duration
    if curSong == n {
      // derive contradiction: curCum == sum_playlist_duration(songs, n)
      if n >= 1 {
        cum_equals_sum(songs, n);
      }
      assert curCum == sum_playlist_duration(songs, n);
      assert curCum < q;
      assert q <= sum_playlist_duration(songs, n);
      assert q <= curCum;
      assert false;
    }
    assert curSong < n;
    // q <= cumulative_duration_at_song(songs, curSong)
    assert cumulative_duration_at_song(songs, curSong) == curCum + songs[curSong].0 * songs[curSong].1;
    assert q <= cumulative_duration_at_song(songs, curSong);

    // Now set the result for this query
    resArr[i] := curSong + 1;
    // Prove 1 <= resArr[i] <= n
    assert 1 <= resArr[i] <= n;

    // Prove the lower-bound condition: either result == 1 or q > cumulative(..., res-2)
    if curSong == 0 {
      assert resArr[i] == 1;
    } else {
      // curCum is cumulative_duration_at_song(songs, curSong - 1) and we have curCum < q
      assert q > cumulative_duration_at_song(songs, curSong - 1);
    }

    i := i + 1;
  }
  result := resArr[..];
}
// </vc-code>

