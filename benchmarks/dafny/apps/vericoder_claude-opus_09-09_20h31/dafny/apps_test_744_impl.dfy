function count_sf_flights(s: string): int
{
    if |s| <= 1 then 0
    else (if s[|s|-1] == 'F' && s[|s|-2] != 'F' then 1 else 0) + count_sf_flights(s[..|s|-1])
}

function count_fs_flights(s: string): int
{
    if |s| <= 1 then 0
    else (if s[|s|-1] == 'S' && s[|s|-2] != 'S' then 1 else 0) + count_fs_flights(s[..|s|-1])
}

// <vc-helpers>
lemma count_sf_flights_lemma(s: string, i: int)
    requires 0 <= i <= |s|
    ensures count_sf_flights(s[..i]) == count_sf_flights_iter(s, i)
{
    if i == 0 {
        assert s[..0] == "";
    } else if i == 1 {
        assert s[..1] == [s[0]];
    } else {
        count_sf_flights_lemma(s, i-1);
        assert s[..i][..i-1] == s[..i-1];
    }
}

function count_sf_flights_iter(s: string, i: int): int
    requires 0 <= i <= |s|
{
    if i <= 1 then 0
    else count_sf_flights_iter(s, i-1) + (if s[i-1] == 'F' && s[i-2] != 'F' then 1 else 0)
}

lemma count_fs_flights_lemma(s: string, i: int)
    requires 0 <= i <= |s|
    ensures count_fs_flights(s[..i]) == count_fs_flights_iter(s, i)
{
    if i == 0 {
        assert s[..0] == "";
    } else if i == 1 {
        assert s[..1] == [s[0]];
    } else {
        count_fs_flights_lemma(s, i-1);
        assert s[..i][..i-1] == s[..i-1];
    }
}

function count_fs_flights_iter(s: string, i: int): int
    requires 0 <= i <= |s|
{
    if i <= 1 then 0
    else count_fs_flights_iter(s, i-1) + (if s[i-1] == 'S' && s[i-2] != 'S' then 1 else 0)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires n >= 2
    requires |s| == n
    requires forall i :: 0 <= i < |s| ==> s[i] == 'S' || s[i] == 'F'
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> count_sf_flights(s) > count_fs_flights(s)
// </vc-spec>
// <vc-code>
{
    var sf_count := 0;
    var fs_count := 0;
    var i := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant sf_count == count_sf_flights_iter(s, i)
        invariant fs_count == count_fs_flights_iter(s, i)
    {
        if s[i] == 'F' && s[i-1] == 'S' {
            sf_count := sf_count + 1;
        } else if s[i] == 'S' && s[i-1] == 'F' {
            fs_count := fs_count + 1;
        }
        i := i + 1;
    }
    
    count_sf_flights_lemma(s, n);
    count_fs_flights_lemma(s, n);
    assert s[..n] == s;
    
    if sf_count > fs_count {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

