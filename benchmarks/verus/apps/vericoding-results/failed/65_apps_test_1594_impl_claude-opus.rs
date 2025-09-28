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
/* helper modified by LLM (iteration 4): Added helpers for reasoning about song sequences */
proof fn lemma_sum_cumulative_relationship(songs: Seq<(int, int)>, n: int)
    requires
        n >= 0,
        songs.len() >= n,
        forall|i: int| #![auto] 0 <= i < n ==> songs[i].0 > 0 && songs[i].1 > 0
    ensures
        sum_playlist_duration(songs, n) == cumulative_duration_at_song(songs, n - 1)
    decreases n
{
    if n == 0 {
        assert(sum_playlist_duration(songs, 0) == 0);
        assert(cumulative_duration_at_song(songs, -1) == 0);
    } else {
        lemma_sum_cumulative_relationship(songs, n - 1);
        assert(sum_playlist_duration(songs, n) == songs[n-1].0 * songs[n-1].1 + sum_playlist_duration(songs, n-1));
        assert(cumulative_duration_at_song(songs, n - 1) == songs[n-1].0 * songs[n-1].1 + cumulative_duration_at_song(songs, n - 2));
    }
}

proof fn lemma_cumulative_increasing(songs: Seq<(int, int)>, i: int, j: int)
    requires
        -1 <= i < j,
        songs.len() > j,
        forall|k: int| #![auto] 0 <= k <= j ==> songs[k].0 > 0 && songs[k].1 > 0
    ensures
        cumulative_duration_at_song(songs, i) < cumulative_duration_at_song(songs, j)
    decreases j - i
{
    if j == i + 1 {
        assert(cumulative_duration_at_song(songs, j) == songs[j].0 * songs[j].1 + cumulative_duration_at_song(songs, j - 1));
        assert(songs[j].0 > 0 && songs[j].1 > 0);
    } else {
        lemma_cumulative_increasing(songs, i, j - 1);
        assert(cumulative_duration_at_song(songs, j) == songs[j].0 * songs[j].1 + cumulative_duration_at_song(songs, j - 1));
        assert(songs[j].0 > 0 && songs[j].1 > 0);
    }
}

spec fn song_duration_spec(song: (i8, i8)) -> int {
    song.0 as int * song.1 as int
}

spec fn cumulative_time_spec(songs: Vec<(i8, i8)>, idx: int) -> int
    recommends
        idx >= -1,
        songs.len() > idx,
        forall|i: int| #![auto] 0 <= i <= idx ==> songs[i].0 > 0 && songs[i].1 > 0
{
    cumulative_duration_at_song(songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int)), idx)
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
    /* code modified by LLM (iteration 4): Added decreases clause to outer while loop */
    let mut result = Vec::new();
    let mut current_song_idx: i8 = 0;
    let mut current_time: i32 = 0;
    let mut query_idx: usize = 0;
    
    if m == 0 {
        return result;
    }
    
    while query_idx < m as usize
        invariant
            query_idx <= m as int,
            result.len() == query_idx,
            0 <= current_song_idx <= n,
            current_time == cumulative_time_spec(songs, current_song_idx as int - 1),
            query_idx > 0 ==> current_time >= queries[query_idx as int - 1] as int,
            forall|i: int| #![auto] 0 <= i < query_idx ==> 1 <= result[i] as int <= n as int,
            forall|i: int| #![auto] 0 <= i < query_idx ==> queries[i] as int <= cumulative_time_spec(songs, result[i] as int - 1),
            forall|i: int| #![auto] 0 <= i < query_idx ==> result[i] as int == 1 || queries[i] as int > cumulative_time_spec(songs, result[i] as int - 2),
        decreases m as int - query_idx as int
    {
        let target_time = queries[query_idx] as i32;
        
        while current_song_idx < n && current_time < target_time
            invariant
                0 <= current_song_idx <= n,
                current_time == cumulative_time_spec(songs, current_song_idx as int - 1),
                query_idx < m as int,
                target_time == queries@[query_idx as int] as int,
            decreases n as int - current_song_idx as int
        {
            let song_duration = (songs[current_song_idx as usize].0 as i32) * (songs[current_song_idx as usize].1 as i32);
            current_time = current_time + song_duration;
            current_song_idx = current_song_idx + 1;
            
            proof {
                assert(song_duration == song_duration_spec(songs[current_song_idx as int - 1]));
                assert(current_time == cumulative_time_spec(songs, current_song_idx as int - 1));
            }
        }
        
        assert(current_song_idx > 0);
        assert(current_time >= target_time);
        assert(target_time <= cumulative_time_spec(songs, current_song_idx as int - 1));
        
        if current_song_idx > 1 {
            proof {
                let songs_int = songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int));
                lemma_cumulative_increasing(songs_int, current_song_idx as int - 2, current_song_idx as int - 1);
            }
        }
        
        result.push(current_song_idx);
        query_idx = query_idx + 1;
    }
    
    proof {
        let songs_int = songs@.map(|i: int, p: (i8, i8)| (p.0 as int, p.1 as int));
        lemma_sum_cumulative_relationship(songs_int, n as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}