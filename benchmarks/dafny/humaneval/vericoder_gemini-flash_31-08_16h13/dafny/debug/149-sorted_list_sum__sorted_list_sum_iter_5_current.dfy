function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
{
  assume{:axiom} false;
}
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
  assume{:axiom} false;
}

// <vc-helpers>
function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreasing |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}

method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    decreases |list|
{
    if |list| <= 1 then
        return list;
    else
    {
        var pivot := list[|list| / 2];
        var less: seq<string> := [];
        var greater: seq<string> := [];
        var equal: seq<string> := [];

        for i := 0 to |list| - 1
            invariant 0 <= i <= |list|
            invariant multiset(less) + multiset(greater) + multiset(equal) == multiset(list[..i])
            invariant forall x :: x in set(less) ==> |x| % 2 == 0
            invariant forall x :: x in set(greater) ==> |x| % 2 == 0
            invariant forall x :: x in set(equal) ==> |x| % 2 == 0
            decreases |list| - i
        {
            if |list[i]| < |pivot| then
                less := less + [list[i]];
            else if |list[i]| > |pivot| then
                greater := greater + [list[i]];
            else
                equal := equal + [list[i]];
        }

        var sorted_less := sort_lengths(less);
        var sorted_greater := sort_lengths(greater);

        return sorted_less + equal + sorted_greater;
    }
}
// </vc-helpers>

// <vc-spec>
method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
// </vc-spec>
// <vc-code>
{
  var evens: seq<string> := [];
  for i := 0 to |list| - 1
    invariant 0 <= i <= |list|
    invariant forall j : int :: 0 <= j < |evens| ==> |evens[j]| % 2 == 0
    invariant multiset(evens) <= multiset(list[..i])
  {
    if |list[i]| % 2 == 0 then
      evens := evens + [list[i]];
    }
  sorted := sort_lengths(evens);
}
// </vc-code>

