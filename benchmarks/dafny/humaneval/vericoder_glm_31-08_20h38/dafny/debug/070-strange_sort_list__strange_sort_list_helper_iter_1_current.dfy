

// <vc-helpers>
function method MinIndex(s: seq<int>, start: int): int
    requires 0 <= start < |s|
    ensures 0 <= MinIndex(s, start) < |s|
    ensures forall i :: start <= i < |s| ==> s[MinIndex(s, start)] <= s[i]
{
    if start == |s| - 1 then
        start
    else
        var min_rest := MinIndex(s, start + 1);
        if s[start] <= s[min_rest] then start else min_rest
}

function method MinIndexValid(s: seq<int>, start: int): bool
    requires 0 <= start < |s|
    ensures MinIndexValid(s, start) ==> 0 <= MinIndex(s, start) < |s| && forall i :: start <= i < |s| ==> s[MinIndex(s, start)] <= s[i]
{
    var min_idx := MinIndex(s, start);
    0 <= min_idx < |s| && forall i :: start <= i < |s| ==> s[min_idx] <= s[i]
}

function method SwapSeq(s: seq<int>, i: int, j: int): seq<int>
    requires 0 <= i < |s| && 0 <= j < |s|
    ensures |SwapSeq(s, i, j)| == |s|
    ensures multiset(SwapSeq(s, i, j)) == multiset(s)
    ensures SwapSeq(s, i, j)[i] == s[j]
    ensures SwapSeq(s, i, j)[j] == s[i]
    ensures forall k :: k != i && k != j ==> SwapSeq(s, i, j)[k] == s[k]
{
    if i == j then s else
    seq k, n => if n == i then s[j] else if n == j then s[i] else s[k][n]
}

predicate IsSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function method IsSortedValid(s: seq<int>): bool
    ensures IsSortedValid(s) == IsSorted(s)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function method Sorted(s: seq<int>): seq<int>
    ensures IsSorted(Sorted(s))
    ensures multiset(Sorted(s)) == multiset(s)
{
    if |s| <= 1 then s else
        var min_idx := MinIndex(s, 0);
        var swapped := SwapSeq(s, 0, min_idx);
        s[0] + Sorted(swapped[1..])
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(s);
  var strange_temp := seq |s|, _ => 0;
  
  ghost var constructed_sorted := seq |s|, _ => 0;

  for i := 0 to |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant |s| == |sorted| == |strange_temp|
    invariant multiset(s) == multiset(sorted)
    invariant multiset(strange_temp) == multiset(s)
    invariant forall k :: 0 < k < |s| -> strange_temp[k] == 0
    invariant forall k :: 0 <= k < 2*i -> 
      (k % 2 == 0 ==> strange_temp[k] == sorted[k / 2]) && 
      (k % 2 == 1 ==> strange_temp[k] == sorted[|s| - (k - 1) / 2 - 1])
    invariant constructed_sorted == sorted[..i] + sorted[|s| - i..]
  {
    if 2*i < |s| {
      strange_temp := strange_temp[2*i := sorted[i]];
    }
    
    if (2*i + 1) < |s| {
      strange_temp := strange_temp[(2*i + 1) := sorted[|s| - i - 1]];
    }
    
    constructed_sorted := sorted[..i+1] + sorted[|s| - i - 1..];
  }
  
  strange := strange_temp;
}
// </vc-code>

method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}