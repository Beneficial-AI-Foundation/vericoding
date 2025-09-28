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
/* helper modified by LLM (iteration 4): recursive spec to find song index for query */
spec fn find_song_for_query(songs: Seq<(int,int)>, n: int, q: int) -> int
    requires
        n >= 1,
        songs.len() >= n,
        forall|i: int| #![auto] 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0,
        q >= 1,
        q <= sum_playlist_duration(songs, n),
    ensures
        1 <= result && result <= n,
        q <= cumulative_duration_at_song(songs, result - 1),
        result == 1 || q > cumulative_duration_at_song(songs, result - 2),
    decreases n
{
    if n == 1 {
        1
    } else {
        let prev = sum_playlist_duration(songs, n - 1);
        if q <= prev {
            find_song_for_query(songs, n - 1, q)
        } else {
            n
        }
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
  /* code modified by LLM (iteration 4): iterative scan computing song indices with proper local result and invariants */
  let mut result = Vec::<i8>::new();
  let mut qi: int = 0;
  while qi < m as int
      invariant
          0 <= qi && qi <= m as int,
          result.len() == qi as usize,
      decreases
          m as int - qi
  {
      let q = queries[qi as usize] as int;
      let mut cum: int = 0;
      let mut k: int = 0;
      while k < n as int
          invariant
              0 <= k && k <= n as int,
              cum >= 0,
          decreases
              n as int - k
      {
          let (a, b) = songs[k as usize];
          cum = cum + (a as int) * (b as int);
          if cum >= q {
              break;
          }
          k = k + 1;
      }
      result.push((k + 1) as i8);
      qi = qi + 1;
  }
  result
}
// </vc-code>


}

fn main() {}