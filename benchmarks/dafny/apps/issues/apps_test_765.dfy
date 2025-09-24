// <vc-preamble>
function count_song_starts(t: int, s: int, q: int): int
    requires 1 <= s < t <= 100000
    requires 2 <= q <= 10000
{
    count_song_starts_from_state(t, s, q, s, 1, 0)
}

function count_song_starts_from_state(t: int, s: int, q: int, s_current: int, a: int, l: int): int
    requires 1 <= s < t <= 100000
    requires 2 <= q <= 10000
    requires a >= 1
    requires l >= 0
    requires s_current >= s
    requires s_current <= t
    decreases t - s_current
{
    if t <= s_current then a
    else
        var new_l := if l + q < t then l + q else t;
        var new_s := if s_current + q - 1 < t then s_current + q - 1 else t;
        if new_l >= new_s && new_s != t then
            count_song_starts_from_state(t, s, q, new_s, a + 1, 0)
        else
            count_song_starts_from_state(t, s, q, new_s, a, new_l)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(t: int, s: int, q: int) returns (result: int)
    requires 1 <= s < t <= 100000
    requires 2 <= q <= 10000
    ensures result >= 1
    ensures result == count_song_starts(t, s, q)
// </vc-spec>
// <vc-code>
{
    var a := 1;
    var l := 0;
    var s_current := s;

    while t > s_current
        invariant a >= 1
        invariant l >= 0
        invariant s_current >= s
        invariant s_current <= t
        invariant count_song_starts(t, s, q) == count_song_starts_from_state(t, s, q, s_current, a, l)
    {
        l := l + q;
        l := if l < t then l else t;
        s_current := s_current + q - 1;
        s_current := if s_current < t then s_current else t;
        if l >= s_current && s_current != t {
            a := a + 1;
            l := 0;
        }
    }

    result := a;
}
// </vc-code>
