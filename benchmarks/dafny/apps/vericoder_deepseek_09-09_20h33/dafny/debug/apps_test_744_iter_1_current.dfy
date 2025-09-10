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
lemma count_sf_flights_recursive(s: string, k: nat)
    requires k <= |s|
    ensures count_sf_flights(s[..k]) ==
        if k <= 1 then 0
        else (if s[k-1] == 'F' && s[k-2] != 'F' then 1 else 0) + count_sf_flights(s[..k-1])
{
    if k <= 1 {
    } else {
        count_sf_flights_recursive(s, k-1);
    }
}

lemma count_fs_flights_recursive(s: string, k: nat)
    requires k <= |s|
    ensures count_fs_flights(s[..k]) ==
        if k <= 1 then 0
        else (if s[k-1] == 'S' && s[k-2] != 'S' then 1 else 0) + count_fs_flights(s[..k-1])
{
    if k <= 1 {
    } else {
        count_fs_flights_recursive(s, k-1);
    }
}

lemma count_sf_vs_fs_property(s: string)
    requires |s| >= 2
    requires forall i :: 0 <= i < |s| ==> s[i] == 'S' || s[i] == 'F'
    ensures count_sf_flights(s) > count_fs_flights(s) <==> s[|s|-1] == 'F'
{
    if |s| <= 1 {
    } else {
        count_sf_flights_recursive(s, |s|);
        count_fs_flights_recursive(s, |s|);
        
        var last_char := s[|s|-1];
        var second_last := s[|s|-2];
        
        if last_char == 'F' {
            if second_last != 'F' {
                // Both counts increase but SF increases by 1 more
                assert count_sf_flights(s) == 1 + count_sf_flights(s[..|s|-1]);
                assert count_fs_flights(s) == count_fs_flights(s[..|s|-1]);
                assert count_sf_flights(s) > count_fs_flights(s);
            } else {
                // Both counts remain the same
                assert count_sf_flights(s) == count_sf_flights(s[..|s|-1]);
                assert count_fs_flights(s) == count_fs_flights(s[..|s|-1]);
            }
        } else { // last_char == 'S'
            if second_last != 'S' {
                // FS increases by 1, SF stays the same
                assert count_sf_flights(s) == count_sf_flights(s[..|s|-1]);
                assert count_fs_flights(s) == 1 + count_fs_flights(s[..|s|-1]);
                assert count_fs_flights(s) > count_sf_flights(s);
            } else {
                // Both counts remain the same
                assert count_sf_flights(s) == count_sf_flights(s[..|s|-1]);
                assert count_fs_flights(s) == count_fs_flights(s[..|s|-1]);
            }
        }
    }
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
    if s[|s|-1] == 'F' {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

