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
/* helper modified by LLM (iteration 5): no ghost type usage in concrete function */
spec fn get_song_len(songs: Seq<(i8, i8)>, song_idx: int)
  recommends
    0 <= song_idx < songs.len()
  {
    songs[song_idx].0 as int * songs[song_idx].1 as int
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
/* code modified by LLM (iteration 5): removed ghost type usage in concrete code */
{
    let mut result: Vec<i8> = Vec::new();
    let mut current_song_idx: i8 = 0;
    let mut current_cumulative_duration: i64 = 0; // Changed to i64 for concrete execution

    let song_data = songs@.map(|i, p: (i8, i8)| (p.0 as int, p.1 as int));

    if m == 0 {
        return result;
    }

    // Populate initial result vector with dummy values, then update
    let queries_vec_len = queries.len();
    while result.len() < queries_vec_len
        invariant
            result.len() <= queries_vec_len,
            queries_vec_len == m as nat
        decreases queries_vec_len - result.len()
    {
        result.push(0);
    }

    let mut query_idx: i8 = 0;
    while query_idx < m
        invariant
            0 <= query_idx <= m,
            0 <= current_song_idx <= n,
            current_song_idx == 0 ==> current_cumulative_duration == 0,
            current_song_idx > 0 ==> current_cumulative_duration == cumulative_duration_at_song(song_data, current_song_idx as int - 1) as i64,
            queries.len() == m as nat,
            songs.len() == n as nat,
            forall|i: int| #![trigger songs[i]] 0 <= i < n as int ==> songs[i].0 > 0 && songs[i].1 > 0,
            forall|i: int| #![trigger queries[i]] 0 <= i < m as int - 1 ==> queries[i] < queries[i + 1],
            forall|i: int| #![trigger queries[i]] 0 <= i < m as int ==> queries[i] >= 1,
            forall|k: int| 0 <= k < query_idx as int ==> 1 <= result[k] as int <= n as int,
            // Post-conditions for already processed queries
            forall|k: int| 0 <= k < query_idx as int ==> queries[k] as int <= cumulative_duration_at_song(song_data, result[k] as int - 1),
            forall|k: int| 0 <= k < query_idx as int ==> result[k] as int == 1 || queries[k] as int > cumulative_duration_at_song(song_data, result[k] as int - 2)
        decreases m - query_idx
    {
        let target_duration = queries[query_idx as usize] as i64; // Changed to i64 for concrete execution

        while current_cumulative_duration < target_duration
            invariant
                0 <= current_song_idx <= n,
                0 <= query_idx <= m,
                (current_song_idx == 0 ==> current_cumulative_duration == 0),
                (current_song_idx > 0 ==> current_cumulative_duration == cumulative_duration_at_song(song_data, current_song_idx as int - 1) as i64),
                current_cumulative_duration < target_duration ==> current_song_idx < n,
                target_duration == queries[query_idx as usize] as i64,
                n == song_data.len() as i8
            decreases n - current_song_idx
        {
            assert(current_song_idx < n) by {
                if current_song_idx == n {
                    // If current_song_idx is n, then current_cumulative_duration is the total duration.
                    // The ensures m == 0 || queries[(m-1) as int] as int <= sum_playlist_duration(...) ensures that the largest query is no more than the total duration.
                    // Since queries are sorted, target_duration <= total_duration.
                    // So, current_cumulative_duration (total_duration) must be >= target_duration.
                    // This contradicts current_cumulative_duration < target_duration.
                    // Therefore, current_song_idx must be < n as int if current_cumulative_duration < target_duration.
                    assert(n as int == song_data.len());
                    assert(sum_playlist_duration(song_data, n as int) == cumulative_duration_at_song(song_data, n as int - 1));
                    assert(query_idx as int <= m as int - 1);
                    assert(queries[query_idx as usize] as int <= queries[(m-1) as usize] as int);
                    assert(queries[(m-1) as usize] as int <= sum_playlist_duration(song_data, n as int));
                    assert(target_duration as int <= sum_playlist_duration(song_data, n as int));
                    if current_cumulative_duration < target_duration && current_song_idx == n {
                        assert(cumulative_duration_at_song(song_data, n as int - 1) == sum_playlist_duration(song_data, n as int));
                        assert(current_cumulative_duration == sum_playlist_duration(song_data, n as int) as i64);
                        assert(current_cumulative_duration as int >= target_duration as int);
                        assert(false); // Contradiction: current_cumulative_duration < target_duration
                    }
                }
            }
            let song_duration = songs[current_song_idx as usize].0 as i64 * songs[current_song_idx as usize].1 as i64; // Changed to i64
            current_cumulative_duration = current_cumulative_duration + song_duration;
            current_song_idx = current_song_idx + 1;
        }

        result.set(query_idx as usize, current_song_idx);
        query_idx = query_idx + 1;
    }

    result
  }
// </vc-code>


}

fn main() {}