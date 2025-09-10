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
lemma count_sf_flights_property(s: string)
    requires |s| >= 1
    ensures count_sf_flights(s) >= 0
{
    if |s| <= 1 {
    } else {
        count_sf_flights_property(s[..|s|-1]);
    }
}

lemma count_fs_flights_property(s: string)
    requires |s| >= 1
    ensures count_fs_flights(s) >= 0
{
    if |s| <= 1 {
    } else {
        count_fs_flights_property(s[..|s|-1]);
    }
}

lemma count_sf_flights_split(s: string, i: int)
    requires 0 <= i <= |s|
    ensures count_sf_flights(s) == count_sf_flights(s[..i]) + count_sf_flights(s[i..])
{
    if i == 0 {
        assert s[..i] == "";
        assert count_sf_flights(s[..i]) == 0;
    } else if i == |s| {
        assert s[i..] == "";
        assert count_sf_flights(s[i..]) == 0;
    } else {
        if |s| <= 1 {
            // Base case
        } else {
            // Recursive case
            count_sf_flights_split(s[..|s|-1], i);
            if i == |s|-1 {
                // Handle boundary case
            } else if i < |s|-1 {
                // s[i..] = s[i..|s|-1] + s[|s|-1..]
                assert s[i..] == s[i..|s|-1] + [s[|s|-1]];
            }
        }
    }
}

lemma count_fs_flights_split(s: string, i: int)
    requires 0 <= i <= |s|
    ensures count_fs_flights(s) == count_fs_flights(s[..i]) + count_fs_flights(s[i..])
{
    if i == 0 {
        assert s[..i] == "";
        assert count_fs_flights(s[..i]) == 0;
    } else if i == |s| {
        assert s[i..] == "";
        assert count_fs_flights(s[i..]) == 0;
    } else {
        if |s| <= 1 {
            // Base case
        } else {
            // Recursive case
            count_fs_flights_split(s[..|s|-1], i);
            if i == |s|-1 {
                // Handle boundary case
            } else if i < |s|-1 {
                // s[i..] = s[i..|s|-1] + s[|s|-1..]
                assert s[i..] == s[i..|s|-1] + [s[|s|-1]];
            }
        }
    }
}

lemma count_sf_flights_step(s: string, i: int)
    requires 1 <= i < |s|
    ensures count_sf_flights(s[..i+1]) == count_sf_flights(s[..i]) + (if s[i] == 'F' && s[i-1] != 'F' then 1 else 0)
{
    var prefix := s[..i+1];
    var shorter := s[..i];
    
    if |prefix| <= 1 {
        // trivial case
    } else {
        assert prefix == shorter + [s[i]];
        assert prefix[|prefix|-1] == s[i];
        assert prefix[|prefix|-2] == s[i-1];
    }
}

lemma count_fs_flights_step(s: string, i: int)
    requires 1 <= i < |s|
    ensures count_fs_flights(s[..i+1]) == count_fs_flights(s[..i]) + (if s[i] == 'S' && s[i-1] != 'S' then 1 else 0)
{
    var prefix := s[..i+1];
    var shorter := s[..i];
    
    if |prefix| <= 1 {
        // trivial case
    } else {
        assert prefix == shorter + [s[i]];
        assert prefix[|prefix|-1] == s[i];
        assert prefix[|prefix|-2] == s[i-1];
    }
}

method count_sf_flights_iterative(s: string) returns (count: int)
    requires |s| >= 2
    requires forall i :: 0 <= i < |s| ==> s[i] == 'S' || s[i] == 'F'
    ensures count == count_sf_flights(s)
{
    count := 0;
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant count == count_sf_flights(s[..i])
    {
        count_sf_flights_step(s, i);
        if s[i] == 'F' && s[i-1] != 'F' {
            count := count + 1;
        }
        i := i + 1;
    }
    assert i == |s|;
    assert s[..i] == s;
}

method count_fs_flights_iterative(s: string) returns (count: int)
    requires |s| >= 2
    requires forall i :: 0 <= i < |s| ==> s[i] == 'S' || s[i] == 'F'
    ensures count == count_fs_flights(s)
{
    count := 0;
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant count == count_fs_flights(s[..i])
    {
        count_fs_flights_step(s, i);
        if s[i] == 'S' && s[i-1] != 'S' {
            count := count + 1;
        }
        i := i + 1;
    }
    assert i == |s|;
    assert s[..i] == s;
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
    var sf_count := count_sf_flights_iterative(s);
    var fs_count := count_fs_flights_iterative(s);
    
    if sf_count > fs_count {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

