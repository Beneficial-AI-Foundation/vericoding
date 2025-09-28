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
/* helper modified by LLM (iteration 3): added ghost function to map song sequence */
spec fn map_songs(songs: Seq<(i8, i8)>) -> Seq<(int, int)> {
    songs.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int))
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
/* code modified by LLM (iteration 5): moved ghost variable declaration to the top of function body */
{
    ghost let mapped_seq = map_songs(songs@);
    let mut cumulative = Vec::new();
    cumulative.push(0i64);

    for i in 0..n
        invariant 
            cumulative.len() == i as usize + 1,
            forall|j: int| 0 <= j <= i ==> cumulative[j as usize] == cumulative_duration_at_song(mapped_seq, j-1)
    {
        let song = songs[i as usize];
        let duration = (song.0 as i64) * (song.1 as i64);
        let next = cumulative[i as usize] + duration;
        cumulative.push(next);
        assert(cumulative[(i+1) as usize] == cumulative_duration_at_song(mapped_seq, i));
    }

    let mut result = Vec::new();
    for i in 0..m
        invariant 
            result.len() == i as usize,
            forall|k: int| 0 <= k < i ==> 1 <= result[k] as int <= n as int,
            forall|k: int| 0 <= k < i ==> queries[k] as int <= cumulative_duration_at_song(mapped_seq, result[k] as int - 1),
            forall|k: int| 0 <= k < i ==> (result[k] as int == 1 || queries[k] as int > cumulative_duration_at_song(mapped_seq, result[k] as int - 2))
    {
        let q_val = queries[i as usize] as i64;
        let mut j = 1;
        while j <= n
            invariant 
                1 <= j <= n+1,
                cumulative[j-1] < q_val
        {
            if cumulative[j as usize] >= q_val {
                break;
            }
            j += 1;
        }
        result.push(j as i8);
    }
    result
}
// </vc-code>


}

fn main() {}