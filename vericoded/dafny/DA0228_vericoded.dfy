predicate ValidInput(a: seq<int>, b: seq<int>, n: int)
{
    |a| >= 0 && |b| >= 0 &&
    (forall i :: 0 <= i < |a| ==> a[i] >= 0) &&
    (forall j :: 0 <= j < |b| ==> b[j] >= 0) &&
    n >= 1
}

function sum_seq(s: seq<int>): int
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

function ShelvesNeeded(total: int, capacity: int): int
    requires capacity > 0
{
    if total == 0 then 0 else (total - 1) / capacity + 1
}

predicate CanPlaceAll(a: seq<int>, b: seq<int>, n: int)
    requires ValidInput(a, b, n)
{
    var total_cups := sum_seq(a);
    var total_medals := sum_seq(b);
    var shelves_for_cups := ShelvesNeeded(total_cups, 5);
    var shelves_for_medals := ShelvesNeeded(total_medals, 10);
    shelves_for_cups + shelves_for_medals <= n
}

// <vc-helpers>
lemma sum_seq_append_single(s: seq<int>, i: int)
    requires forall j :: 0 <= j < |s| ==> s[j] >= 0
    requires 0 <= i < |s|
    ensures sum_seq(s[..i+1]) == sum_seq(s[..i]) + s[i]
{
    var prefix := s[..i];
    var extended := s[..i+1];
    
    assert extended == prefix + [s[i]];
    
    if |prefix| == 0 {
        assert prefix == [];
        assert extended == [s[i]];
        assert sum_seq(extended) == s[i];
        assert sum_seq(prefix) == 0;
    } else {
        assert extended[0] == prefix[0];
        assert extended[1..] == prefix[1..] + [s[i]];
        sum_seq_append(prefix[1..], s[i]);
    }
}

lemma sum_seq_append(s: seq<int>, x: int)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    requires x >= 0
    ensures sum_seq(s + [x]) == sum_seq(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert sum_seq([x]) == x;
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
        sum_seq_append(s[1..], x);
    }
}

method sum_array(s: seq<int>) returns (total: int)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures total == sum_seq(s)
{
    total := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant total == sum_seq(s[..i])
    {
        sum_seq_append_single(s, i);
        total := total + s[i];
        i := i + 1;
    }
    
    assert s[..|s|] == s;
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>, n: int) returns (result: string)
    requires ValidInput(a, b, n)
    ensures result == (if CanPlaceAll(a, b, n) then "YES" else "NO")
// </vc-spec>
// <vc-code>
{
    var total_cups := sum_array(a);
    var total_medals := sum_array(b);
    
    var shelves_for_cups := if total_cups == 0 then 0 else (total_cups - 1) / 5 + 1;
    var shelves_for_medals := if total_medals == 0 then 0 else (total_medals - 1) / 10 + 1;
    
    assert shelves_for_cups == ShelvesNeeded(total_cups, 5);
    assert shelves_for_medals == ShelvesNeeded(total_medals, 10);
    
    if shelves_for_cups + shelves_for_medals <= n {
        result := "YES";
    } else {
        result := "NO";
    }
    
    assert result == (if CanPlaceAll(a, b, n) then "YES" else "NO");
}
// </vc-code>

