// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_playlist_duration(songs: Seq<(int, int)>, n: int) -> int
  recommends 
    n >= 0,
    songs.len() >= n,
    forall|i: int| #![auto] 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0
  decreases n
  when n >= 0 && songs.len() >= n
{
  if n == 0 { 
    0 
  } else { 
    songs[n-1].0 * songs[n-1].1 + sum_playlist_duration(songs, n-1) 
  }
}

spec fn cumulative_duration_at_song(songs: Seq<(int, int)>, song_idx: int) -> int
  recommends 
    song_idx >= -1,
    songs.len() > song_idx,
    forall|i: int| #![auto] 0 <= i <= song_idx ==> songs[i].0 > 0 && songs[i].1 > 0
  decreases song_idx + 1
  when song_idx >= -1 && songs.len() > song_idx
{
  if song_idx == -1 { 
    0 
  } else { 
    songs[song_idx].0 * songs[song_idx].1 + cumulative_duration_at_song(songs, song_idx - 1) 
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma body with proper base case assertion */
proof fn lemma_cumulative_duration_monotonic(songs: Seq<(int, int)>, i: int, j: int)
  requires
    i >= -1,
    j >= i,
    songs.len() > j,
    forall|k: int| #![auto] 0 <= k <= j ==> songs[k].0 > 0 && songs[k].1 > 0
  ensures
    cumulative_duration_at_song(songs, i) <= cumulative_duration_at_song(songs, j)
  decreases j - i
{
  if i == j {
  } else {
    lemma_cumulative_duration_monotonic(songs, i, j - 1);
  }
}

proof fn lemma_cumulative_duration_positive(songs: Seq<(int, int)>, i: int)
  requires
    i >= 0,
    songs.len() > i,
    forall|k: int| #![auto] 0 <= k <= i ==> songs[k].0 > 0 && songs[k].1 > 0
  ensures
    cumulative_duration_at_song(songs, i) > 0
  decreases i + 1
{
  if i == 0 {
    assert(cumulative_duration_at_song(songs, 0) == songs[0].0 * songs[0].1 + cumulative_duration_at_song(songs, -1));
    assert(cumulative_duration_at_song(songs, -1) == 0);
    assert(songs[0].0 > 0 && songs[0].1 > 0);
  } else {
    lemma_cumulative_duration_positive(songs, i - 1);
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, songs: Vec<(i8, i8)>, queries: Vec<i8>) -> (result: Vec<i8>)
  requires 
    n >= 0,
    m >= 0,
    songs.len() == n as nat,
    queries.len() == m as nat,
    forall|i: int| #![trigger songs[i]] 0 <= i < n as int ==> songs[i].0 > 0 && songs[i].1 > 0,
    forall|i: int| #![trigger queries[i]] 0 <= i < m as int - 1 ==> queries[i] < queries[i + 1],
    forall|i: int| #![trigger queries[i]] 0 <= i < m as int ==> queries[i] >= 1,
    m == 0 || queries[(m-1) as int] as int <= sum_playlist_duration(songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int)), n as int)
  ensures 
    result.len() == m as nat,
    forall|i: int| #![trigger result[i]] 0 <= i < m as int ==> 1 <= result[i] as int <= n as int,
    forall|i: int| #![trigger result[i]] 0 <= i < m as int ==> queries[i] as int <= cumulative_duration_at_song(songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int)), result[i] as int - 1),
    forall|i: int| #![trigger result[i]] 0 <= i < m as int ==> result[i] as int == 1 || queries[i] as int > cumulative_duration_at_song(songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int)), result[i] as int - 2)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed bounds checking and loop invariants */
  let mut result: Vec<i8> = Vec::new();
  let mut query_idx = 0usize;
  
  while query_idx < m as usize
    invariant
      query_idx <= m as usize,
      result.len() == query_idx,
      forall|i: int| #![trigger result[i]] 0 <= i < query_idx as int ==> 1 <= result[i] as int <= n as int,
      forall|i: int| #![trigger result[i]] 0 <= i < query_idx as int ==> queries[i] as int <= cumulative_duration_at_song(songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int)), result[i] as int - 1),
      forall|i: int| #![trigger result[i]] 0 <= i < query_idx as int ==> result[i] as int == 1 || queries[i] as int > cumulative_duration_at_song(songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int)), result[i] as int - 2)
    decreases m as usize - query_idx
  {
    assert(query_idx < queries.len());
    let query = queries[query_idx];
    let mut song_idx = 0usize;
    let mut cumulative = 0i32;
    
    while song_idx < n as usize
      invariant
        song_idx <= n as usize,
        cumulative as int == cumulative_duration_at_song(songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int)), song_idx as int - 1)
      decreases n as usize - song_idx
    {
      assert(song_idx < songs.len());
      let duration = songs[song_idx].0 as i32 * songs[song_idx].1 as i32;
      cumulative = cumulative + duration;
      
      if cumulative >= query as i32 {
        result.push((song_idx + 1) as i8);
        break;
      }
      
      song_idx = song_idx + 1;
    }
    
    if song_idx >= n as usize {
      result.push(n);
    }
    
    query_idx = query_idx + 1;
  }
  
  result
}
// </vc-code>


}

fn main() {}