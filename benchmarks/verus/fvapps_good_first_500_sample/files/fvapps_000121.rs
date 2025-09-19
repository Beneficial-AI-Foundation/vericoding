// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn num_music_playlists_spec(n: u32, l: u32, k: u32) -> u32;

fn num_music_playlists(n: u32, l: u32, k: u32) -> (result: u32)
    requires 
        n > 0,
        l >= n,
        k < n,
    ensures 
        result < 1000000007,
        result == num_music_playlists_spec(n, l, k),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}

proof fn playlists_bounds(n: u32, l: u32, k: u32) 
    requires 
        n > 0,
        l >= n,
        k < n,
    ensures num_music_playlists_spec(n, l, k) < 1000000007
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn playlists_k_eq_n_minus_one(n: u32, l: u32, k: u32)
    requires 
        n > 0,
        l >= n,
        k == n - 1,
    ensures num_music_playlists_spec(n, l, k) > 0
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn playlists_trivial_cases_one_song()
    ensures num_music_playlists_spec(1, 1, 0) == 1
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn playlists_impossible_cases_one()
    ensures num_music_playlists_spec(1, 2, 1) == 0
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn playlists_impossible_cases_two()
    ensures num_music_playlists_spec(2, 4, 2) == 0
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-code>


}

fn main() {
    // println!("{}", num_music_playlists(3, 3, 1)); // Expected: 6
    // println!("{}", num_music_playlists(2, 3, 0)); // Expected: 6
    // println!("{}", num_music_playlists(2, 3, 1)); // Expected: 2
}