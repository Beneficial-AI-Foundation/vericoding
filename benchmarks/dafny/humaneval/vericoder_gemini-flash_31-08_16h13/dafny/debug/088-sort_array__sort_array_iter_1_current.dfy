

// <vc-helpers>
function method IsPermutation(s1: seq<int>, s2: seq<int>): bool
  reads s1, s2
{
  multiset(s1) == multiset(s2)
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
   var result := SortSeq(s);

  if |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 then
    // Sort in non-increasing order
    // We already have result sorted in non-decreasing order from SortSeq
    // So, reverse it to get non-increasing order
    sorted := reverse(result);
    assert |sorted| == |s| by (
        calc {
            |sorted|;
            |reverse(result)|;
            |result|;
            |s|;
        }
    );
     assert IsPermutation(s, sorted) by (
        calc {
            multiset(sorted);
            multiset(reverse(result));
            multiset(result);
            multiset(s);
        }
     );
  else
    // Sort in non-decreasing order
    sorted := result;
     assert |sorted| == |s| by (
        calc {
            |sorted|;
            |result|;
            |s|;
        }
    );
     assert IsPermutation(s, sorted) by (
        calc {
            multiset(sorted);
            multiset(result);
            multiset(s);
        }
     );
  return sorted;
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
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