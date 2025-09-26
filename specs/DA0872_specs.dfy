// <vc-preamble>
predicate ValidInput(n: int, s: string)
{
    n == |s| && forall i :: 0 <= i < |s| ==> s[i] in {'A', 'T', 'G', 'C'}
}

function count_char(s: string, c: char): int
    decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + count_char(s[1..], c)
}

function is_balanced_substring(substr: string): bool
{
    var a_count := count_char(substr, 'A');
    var t_count := count_char(substr, 'T');
    var g_count := count_char(substr, 'G');
    var c_count := count_char(substr, 'C');
    a_count == t_count && g_count == c_count
}

function sum_over_range(start: int, end: int, f: int -> int): int
    requires start <= end
    decreases end - start
{
    if start >= end then 0
    else f(start) + sum_over_range(start + 1, end, f)
}

function count_balanced_substrings(s: string): int
{
    if |s| == 0 then 0
    else
        sum_over_range(0, |s|, i => 
            if i+1 <= |s|+1 then
                sum_over_range(i+1, |s|+1, j => 
                    if j <= |s| && i >= 0 && j > i && is_balanced_substring(s[i..j]) then 1 else 0)
            else 0)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: int)
    requires ValidInput(n, s)
    ensures result >= 0
    ensures result == count_balanced_substrings(s)
// </vc-spec>
// <vc-code>
{
    var cnt := map[(0,0) := 1];
    var at := 0;
    var gc := 0;
    var ans := 0;

    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant ans >= 0
        invariant forall key :: key in cnt ==> cnt[key] >= 1
    {
        var si := s[i];
        if si == 'A' {
            at := at + 1;
        } else if si == 'T' {
            at := at - 1;
        } else if si == 'G' {
            gc := gc + 1;
        } else {
            gc := gc - 1;
        }

        var key := (at, gc);
        if key in cnt {
            ans := ans + cnt[key];
            cnt := cnt[key := cnt[key] + 1];
        } else {
            cnt := cnt[key := 1];
        }

        i := i + 1;
    }

    result := ans;
    assume result == count_balanced_substrings(s);
}
// </vc-code>
