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
predicate sorted_by_length(sorted: seq<string>)
{
    forall x: int, y: int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
}

lemma MultisetFilterLengthEven(list: seq<string>) returns (filtered: seq<string>)
    ensures |filtered| <= |list|
    ensures forall i :: 0 <= i < |filtered| ==> |filtered[i]| % 2 == 0
    ensures multiset(filtered) <= multiset(list)
    ensures sorted_by_length(filtered)
{
    filtered := [];
    var i := 0;
    while i < |list|
        invariant 0 <= i <= |list|
        invariant |filtered| <= i
        invariant forall j :: 0 <= j < |filtered| ==> |filtered[j]| % 2 == 0
        invariant multiset(filtered) <= multiset(list[0..i])
        invariant sorted_by_length(filtered)
    {
        if |list[i]| % 2 == 0 {
            if |filtered| == 0 {
                filtered := [list[i]];
            } else {
                var pos := |filtered|;
                var j := 0;
                while j < |filtered| && |filtered[j]| <= |list[i]|
                    invariant 0 <= j <= |filtered|
                    invariant forall k :: 0 <= k < j ==> |filtered[k]| <= |list[i]|
                {
                    j := j + 1;
                }
                pos := j;
                filtered := filtered[0..pos] + [list[i]] + filtered[pos..];
            }
        }
        i := i + 1;
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
    var filtered := [];
    var i := 0;
    
    while i < |list|
        invariant 0 <= i <= |list|
        invariant |filtered| <= i
        invariant forall j :: 0 <= j < |filtered| ==> |filtered[j]| % 2 == 0
        invariant multiset(filtered) <= multiset(list[0..i])
        invariant forall x: int, y: int :: 0 <= x < y < |filtered| ==> |filtered[x]| <= |filtered[y]|
    {
        if |list[i]| % 2 == 0 {
            if |filtered| == 0 {
                filtered := [list[i]];
            } else {
                var pos := |filtered|;
                var j := 0;
                while j < |filtered| && |filtered[j]| <= |list[i]|
                    invariant 0 <= j <= |filtered|
                    invariant forall k :: 0 <= k < j ==> |filtered[k]| <= |list[i]|
                {
                    j := j + 1;
                }
                pos := j;
                filtered := filtered[0..pos] + [list[i]] + filtered[pos..];
            }
        }
        i := i + 1;
    }
    
    sorted := filtered;
}
// </vc-code>

