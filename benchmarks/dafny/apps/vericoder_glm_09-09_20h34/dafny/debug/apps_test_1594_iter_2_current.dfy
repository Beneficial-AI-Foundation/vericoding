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
method BinarySearch(songs: seq<(int, int)>, q: int) returns (idx: int)
  requires 0 < |songs|
  requires q > 0
  requires q <= cumulative_duration_at_song(songs, |songs|-1)
  ensures 0 <= idx < |songs|
  ensures cumulative_duration_at_song(songs, idx) >= q
  ensures idx == 0 || cumulative_duration_at_song(songs, idx-1) < q
{
  var low, high := 0, |songs|;
  while low < high
    invariant 0 <= low <= high <= |songs|
    invariant low == 0 || cumulative_duration_at_song(songs, low-1) < q
    invariant high == |songs| || cumulative_duration_at_song(songs, high) >= q
  {
    var mid := (low + high) / 2;
    if cumulative_duration_at_song(songs, mid) < q {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  idx := low;
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
  if m == 0 {
    return [];
  }
  var arr := new int[m];
  for i := 0 to m-1
    invariant 0 <= i <= m
    invariant forall k :: 0 <= k < i ==> 1 <= arr[k] <= n
    invariant forall k :: 0 <= k < i ==> queries[k] <= cumulative_duration_at_song(songs, arr[k]-1)
    invariant forall k :: 0 <= k < i ==> (arr[k] == 1 || queries[k] > cumulative_duration_at_song(songs, arr[k]-2))
  {
    var j := BinarySearch(songs, queries[i]);
    arr[i] := j + 1;
  }
  return arr[..];
}
// </vc-code>

