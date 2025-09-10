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

lemma query_in_bounds(songs: seq<(int, int)>, n: int, m: int, queries: seq<int>, query_idx: int)
  requires n >= 0 && |songs| == n
  requires m >= 0 && |queries| == m
  requires forall i :: 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0
  requires forall i :: 0 <= i < m ==> queries[i] >= 1
  requires m == 0 || queries[m-1] <= sum_playlist_duration(songs, n)
  requires 0 <= query_idx < m
  ensures queries[query_idx] <= sum_playlist_duration(songs, n)
{
  if query_idx == m - 1 {
    assert queries[query_idx] <= sum_playlist_duration(songs, n);
  } else {
    assert queries[query_idx] < queries[m-1];
    assert queries[m-1] <= sum_playlist_duration(songs, n);
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
    invariant query_idx > 0 ==> cumulative_time >= cumulative_duration_at_song(songs, result[query_idx - 1] - 1)
  {
    var query := queries[query_idx];
    query_in_bounds(songs, n, m, queries, query_idx);
    
    // Store the initial state
    var initial_song_idx := song_idx;
    var initial_cumulative := cumulative_time;
    
    while song_idx < n && cumulative_time < query
      invariant 0 <= song_idx <= n
      invariant song_idx == 0 ==> cumulative_time == 0
      invariant song_idx > 0 ==> cumulative_time == cumulative_duration_at_song(songs, song_idx - 1)
      invariant query_idx > 0 ==> song_idx >= result[query_idx - 1]
      invariant initial_song_idx <= song_idx
      invariant song_idx == initial_song_idx ==> cumulative_time == initial_cumulative
      invariant song_idx > initial_song_idx ==> cumulative_duration_at_song(songs, song_idx - 2) < query
    {
      cumulative_time := cumulative_time + songs[song_idx].0 * songs[song_idx].1;
      song_idx := song_idx + 1;
    }
    
    // At this point, either song_idx == n or cumulative_time >= query
    sum_equals_cumulative(songs, n);
    if song_idx == n && cumulative_time < query {
      // This case is impossible because query <= sum_playlist_duration(songs, n)
      assert cumulative_time == cumulative_duration_at_song(songs, n - 1);
      assert cumulative_time == sum_playlist_duration(songs, n);
      assert false;
    }
    
    assert cumulative_time >= query;
    assert song_idx > 0;
    assert cumulative_time == cumulative_duration_at_song(songs, song_idx - 1);
    
    // The query is satisfied at song_idx
    result := result + [song_idx];
    
    // Verify the postconditions for the newly added result
    assert queries[query_idx] <= cumulative_duration_at_song(songs, result[query_idx] - 1);
    
    if song_idx > 1 {
      // We need to show that query > cumulative_duration_at_song(songs, song_idx - 2)
      if song_idx > initial_song_idx {
        // The loop executed at least once, so we have the invariant
        assert cumulative_duration_at_song(songs, song_idx - 2) < query;
      } else {
        // song_idx == initial_song_idx, loop didn't execute
        // This means cumulative_time >= query at the start
        assert initial_song_idx == song_idx;
        assert initial_cumulative >= query;
        assert initial_song_idx > 0;
        assert initial_cumulative == cumulative_duration_at_song(songs, initial_song_idx - 1);
        
        // We need to prove query > cumulative_duration_at_song(songs, song_idx - 2)
        // Since song_idx > 1 and the loop didn't execute, we had cumulative_time >= query initially
        // But this means the previous iteration must have stopped at song_idx - 1 or earlier
        if query_idx > 0 {
          assert result[query_idx - 1] <= song_idx;
          assert queries[query_idx - 1] < query;
          if result[query_idx - 1] == song_idx {
            assert queries[query_idx - 1] <= cumulative_duration_at_song(songs, song_idx - 1);
            assert queries[query_idx - 1] > cumulative_duration_at_song(songs, song_idx - 2);
            assert query > cumulative_duration_at_song(songs, song_idx - 2);
          } else {
            assert result[query_idx - 1] < song_idx;
            cumulative_duration_monotonic(songs, result[query_idx - 1] - 1, song_idx - 2);
            assert query > cumulative_duration_at_song(songs, song_idx - 2);
          }
        } else {
          // query_idx == 0, so this is the first query
          // initial_song_idx == 0 would mean cumulative_time == 0, but then cumulative_time < query
          assert song_idx > 0;
          assert cumulative_time >= query;
          assert false; // This case shouldn't happen for the first query
        }
      }
    }
  }
}
// </vc-code>

