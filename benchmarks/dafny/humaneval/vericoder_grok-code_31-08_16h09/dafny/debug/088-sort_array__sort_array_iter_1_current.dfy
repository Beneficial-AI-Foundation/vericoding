

// <vc-helpers>
function multiset<T>(s: seq<T>): map<T, int> 
  decreases s
{
  if |s| == 0 then map[]
  else multiset(s[1..])[s[0]] := multiset(s[1..])[s[0]]+1
}

method reverse(s: seq<int>) returns (rev: seq<int>)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  rev := [];
  for i := |s|-1 downto 0 
    invariant 0 <= i <= |s| && |rev| == |s|-1 - i 
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - (i+1 + k)] 
  {
    rev := rev + [s[i]];
  }
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  if |s| == 0 { return []; }
  sorted := [s[0]];
  var i := 1;
  while i < |s|
    invariant i <= |s|
    invariant |sorted| == i
    invariant forall a, b :: 0 <= a < b < |sorted| ==> sorted[a] <= sorted[b]
    invariant multiset(sorted) == multiset(s[..i])
  {
    // insert s[i] into sorted
    var j := 0;
    while j < |sorted| && sorted[j] <= s[i]
      invariant 0 <= j <= |sorted|
      invariant forall k :: 0 <= k < j ==> sorted[k] <= s[i]
    {
      j := j + 1;
    }
    // insert at j
    sorted := sorted[..j] + [s[i]] + sorted[j..];
    i := i + 1;
  }
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
if |s| == 0 {
  sorted := [];
} else {
  var sortedAsc := SortSeq(s);
  var sum := s[0] + s[|s| - 1];
  if sum % 2 == 0 {
    sorted := reverse(sortedAsc);
  } else {
    sorted := sortedAsc;
  }
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