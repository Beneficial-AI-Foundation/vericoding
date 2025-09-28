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
    /* code modified by LLM (iteration 5): fixed compilation error by moving tracked assignment to proof block and added decreases to while loop */
    tracked(song_seq: Seq<(int, int)>) {
        proof {
            song_seq = songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int));
        }
        let mut result = Vec::<i8>::new();
        for q_idx in 0..(m as usize) {
            let q = queries[q_idx];
            let mut current: i64 = 0;
            let mut ghost_current: int = 0;
            let mut idx = 0;
            while idx < (n as usize) && current < (q as i64)
                invariant
                    idx as int <= n as int,
                    ghost_current == cumulative_duration_at_song(song_seq, idx as int - 1),
                    idx as int == 0 ==> ghost_current == 0,
                decreases n as int - idx as int
            {
                current += (songs[idx].0 as i64) * (songs[idx].1 as i64);
                proof {
                    ghost_current = ghost_current + song_seq[idx as int].0 * song_seq[idx as int].1;
                }
                idx += 1;
            }
            result.push(idx as i8);
            proof {
                assert(idx as int >= 1 && idx as int <= n as int);
                assert(ghost_current >= q as int);
                assert(ghost_current == cumulative_duration_at_song(song_seq, idx as int - 1));
                if idx as int > 1 {
                    proof {
                        let prev_ghost = ghost_current - song_seq[idx as int - 1].0 * song_seq[idx as int - 1].1;
                        assert(prev_ghost < q as int);
                        assert(prev_ghost == cumulative_duration_at_song(song_seq, idx as int - 2));
                    }
                }
            }
        }
        result
    }
}
// </vc-code>


}

fn main() {}