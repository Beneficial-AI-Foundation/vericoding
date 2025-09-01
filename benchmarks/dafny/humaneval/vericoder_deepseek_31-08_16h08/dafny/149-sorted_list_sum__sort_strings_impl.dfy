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

// <vc-helpers>
predicate sorted_by_lengths(list: seq<string>)
{
    forall x: int, y: int :: 0 <= x < y < |list| ==> |list[x]| <= |list[y]|
}

predicate all_even_length(list: seq<string>)
{
    forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
}

lemma bubble_up_strings(list: seq<string>) returns (new_list: seq<string>)
    requires all_even_length(list)
    ensures |new_list| == |list| 
    ensures multiset(new_list) == multiset(list)
    ensures all_even_length(new_list)
    ensures sorted_by_lengths(new_list)
    decreases |list|
{
    if |list| <= 1 {
        new_list := list;
    } else {
        var head := list[0];
        var tail := list[1..];
        var sorted_tail := bubble_up_strings(tail);
        new_list := insert_sorted_by_length(head, sorted_tail);
    }
}

lemma insert_sorted_by_length(elem: string, list: seq<string>) returns (new_list: seq<string>)
    requires all_even_length(list)
    requires |elem| % 2 == 0
    requires sorted_by_lengths(list)
    ensures |new_list| == |list| + 1
    ensures multiset(new_list) == multiset(list) + multiset{elem}
    ensures all_even_length(new_list)
    ensures sorted_by_lengths(new_list)
    decreases |list|
{
    if |list| == 0 {
        new_list := [elem];
    } else if |elem| <= |list[0]| {
        new_list := [elem] + list;
    } else {
        var tail_sorted := insert_sorted_by_length(elem, list[1..]);
        new_list := [list[0]] + tail_sorted;
    }
}

lemma swap_preserves_even_lengths(list: seq<string>, i: int, j: int) 
    requires 0 <= i < j < |list|
    requires all_even_length(list)
    ensures all_even_length(list[i := list[j]][j := list[i]])
{
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
    sorted := list;
    if |list| > 1 {
        var i := |list| - 2;
        while (i >= 0)
            invariant -1 <= i < |sorted|
            invariant |sorted| == |list|
            invariant multiset(sorted) == multiset(list)
            invariant all_even_length(sorted)
            invariant forall k: int :: i+1 <= k < |sorted| - 1 ==> |sorted[k]| <= |sorted[k+1]|
            decreases i + 1
        {
            var j := 0;
            while (j <= i)
                invariant 0 <= j <= i+1
                invariant |sorted| == |list|
                invariant multiset(sorted) == multiset(list)
                invariant all_even_length(sorted)
                invariant forall k: int :: 0 <= k < j ==> |sorted[k]| <= |sorted[k+1]|
                invariant forall k: int :: i+1 <= k < |sorted| - 1 ==> |sorted[k]| <= |sorted[k+1]|
                decreases i - j + 1
            {
                if |sorted[j]| > |sorted[j+1]| {
                    var temp := sorted[j];
                    sorted := sorted[j := sorted[j+1]];
                    sorted := sorted[j+1 := temp];
                }
                j := j + 1;
            }
            i := i - 1;
        }
    }
}
// </vc-code>

method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
  assume{:axiom} false;
}
method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}