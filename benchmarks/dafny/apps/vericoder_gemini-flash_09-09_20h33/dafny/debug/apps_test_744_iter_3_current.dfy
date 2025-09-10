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
    var sf_count := count_sf_flights(s);
    var fs_count := count_fs_flights(s);

    if sf_count > fs_count {
        return "YES";
    } else {
        return "NO";
    }
}
// </vc-code>

