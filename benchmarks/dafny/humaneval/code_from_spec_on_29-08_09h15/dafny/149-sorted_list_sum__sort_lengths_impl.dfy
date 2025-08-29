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

// <vc-helpers>
predicate is_sorted_by_length(s: seq<string>)
{
    forall x, y :: 0 <= x < y < |s| ==> |s[x]| <= |s[y]|
}

lemma insertion_sort_maintains_multiset(arr: seq<string>, i: int, key: string, pos: int, new_arr: seq<string>)
    requires 0 <= i < |arr|
    requires 0 <= pos <= i
    requires key == arr[i]
    requires new_arr == arr[..pos] + [key] + arr[pos..i] + arr[i+1..]
    ensures multiset(new_arr) == multiset(arr)
{
    assert arr == arr[..pos] + arr[pos..i] + [key] + arr[i+1..];
    assert multiset(arr[..pos] + arr[pos..i] + [key] + arr[i+1..]) == 
           multiset(arr[..pos]) + multiset(arr[pos..i]) + multiset([key]) + multiset(arr[i+1..]);
    assert multiset(new_arr) == 
           multiset(arr[..pos]) + multiset([key]) + multiset(arr[pos..i]) + multiset(arr[i+1..]);
}

lemma even_length_preserved(arr: seq<string>, i: int, key: string, pos: int, new_arr: seq<string>)
    requires 0 <= i < |arr|
    requires 0 <= pos <= i
    requires key == arr[i]
    requires new_arr == arr[..pos] + [key] + arr[pos..i] + arr[i+1..]
    requires forall j :: 0 <= j < |arr| ==> |arr[j]| % 2 == 0
    ensures forall j :: 0 <= j < |new_arr| ==> |new_arr[j]| % 2 == 0
{
}

lemma sorted_property_maintained(sorted: seq<string>, i: int, pos: int, key: string)
    requires 0 < i < |sorted|
    requires 0 <= pos <= i
    requires key == sorted[i]
    requires is_sorted_by_length(sorted[..pos])
    requires forall k :: pos <= k < i ==> |sorted[k]| > |key|
    requires is_sorted_by_length(sorted[..i])
    ensures is_sorted_by_length((sorted[..pos] + [key] + sorted[pos..i] + sorted[i+1..])[..i+1])
{
    var new_sorted := sorted[..pos] + [key] + sorted[pos..i] + sorted[i+1..];
    
    forall x, y | 0 <= x < y < i + 1
        ensures |new_sorted[x]| <= |new_sorted[y]|
    {
        if y < pos {
            assert new_sorted[x] == sorted[x];
            assert new_sorted[y] == sorted[y];
            assert is_sorted_by_length(sorted[..pos]);
        } else if y == pos {
            assert new_sorted[y] == key;
            if x < pos {
                assert new_sorted[x] == sorted[x];
                if pos > 0 {
                    assert x < pos;
                    assert is_sorted_by_length(sorted[..pos]);
                    assert |sorted[x]| <= |sorted[pos-1]|;
                    assert is_sorted_by_length(sorted[..i]);
                    assert |sorted[pos-1]| <= |sorted[pos]|;
                    assert |sorted[pos]| > |key|;
                } else {
                    assert false;
                }
            }
        } else if pos < y {
            if x < pos {
                assert new_sorted[x] == sorted[x];
                var old_idx := pos + (y - pos - 1);
                assert new_sorted[y] == sorted[old_idx];
                assert old_idx >= pos && old_idx < i;
                assert |sorted[old_idx]| > |key|;
                if pos > 0 {
                    assert is_sorted_by_length(sorted[..pos]);
                    assert |sorted[x]| <= |sorted[pos-1]|;
                    assert is_sorted_by_length(sorted[..i]);
                    assert |sorted[pos-1]| <= |sorted[pos]|;
                    assert |sorted[pos]| > |key|;
                }
            } else if x == pos {
                assert new_sorted[x] == key;
                var old_idx := pos + (y - pos - 1);
                assert new_sorted[y] == sorted[old_idx];
                assert old_idx >= pos && old_idx < i;
                assert |sorted[old_idx]| > |key|;
            } else {
                var old_idx_x := pos + (x - pos - 1);
                var old_idx_y := pos + (y - pos - 1);
                assert new_sorted[x] == sorted[old_idx_x];
                assert new_sorted[y] == sorted[old_idx_y];
                assert old_idx_x >= pos && old_idx_x < i;
                assert old_idx_y >= pos && old_idx_y < i;
                assert old_idx_x < old_idx_y;
                assert is_sorted_by_length(sorted[..i]);
                assert |sorted[old_idx_x]| <= |sorted[old_idx_y]|;
            }
        }
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
Sort elements. Requires: the condition holds for all values. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
// </vc-spec>

// <vc-code>
{
    if |list| == 0 {
        sorted := list;
        return;
    }
    
    sorted := list;
    
    var i := 1;
    while i < |sorted|
        invariant 1 <= i <= |sorted|
        invariant |sorted| == |list|
        invariant multiset(sorted) == multiset(list)
        invariant forall j :: 0 <= j < |sorted| ==> |sorted[j]| % 2 == 0
        invariant is_sorted_by_length(sorted[..i])
    {
        var key := sorted[i];
        var j := i - 1;
        
        while j >= 0 && |sorted[j]| > |key|
            invariant -1 <= j <= i - 1
            invariant sorted[i] == key
            invariant forall k :: j + 1 <= k < i ==> |sorted[k]| > |key|
            invariant is_sorted_by_length(sorted[..j+1])
        {
            j := j - 1;
        }
        
        var pos := j + 1;
        var old_sorted := sorted;
        sorted := sorted[..pos] + [key] + sorted[pos..i] + sorted[i+1..];
        
        insertion_sort_maintains_multiset(old_sorted, i, key, pos, sorted);
        even_length_preserved(old_sorted, i, key, pos, sorted);
        sorted_property_maintained(old_sorted, i, pos, key);
        
        i := i + 1;
    }
}
// </vc-code>

method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}