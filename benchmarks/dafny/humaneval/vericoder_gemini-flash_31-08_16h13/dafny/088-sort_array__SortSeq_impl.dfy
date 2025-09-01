method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
{
  assume{:axiom} false;
}
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function multiset<T>(s: seq<T>): multiset<T>
{
  multiset(s[k] | k in 0 .. |s|)
}

lemma lemma_multiset_append<T>(s: seq<T>, t: seq<T>)
  ensures multiset(s + t) == multiset(s) + multiset(t)
{ }

lemma lemma_multiset_single<T>(s: seq<T>, x: T)
  ensures multiset(s + [x]) == multiset(s) + multiset{x}
{ }

lemma lemma_multiset_split<T>(s: seq<T>, i: int)
  requires 0 <= i <= |s|
  ensures multiset(s) == multiset(s[0..i]) + multiset(s[i..|s|])
{ }

lemma lemma_multiset_empty<T>()
  ensures multiset([]) == multiset{}
{ }
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 then
    return [];
  else if |s| == 1 then
    return s;
  else
    var mid := |s| / 2;
    var left := SortSeq(s[0..mid]);
    var right := SortSeq(s[mid..|s|]);
    var merged := [];
    var i := 0;
    var j := 0;
    
    lemma_multiset_split(s, mid);

    while i < |left| || j < |right|
      invariant 0 <= i <= |left|
      invariant 0 <= j <= |right|
      invariant forall x, y :: 0 <= x < y < |merged| ==> merged[x] <= merged[y]
      invariant multiset(merged) + multiset(left[i..]) + multiset(right[j..]) == multiset(left) + multiset(right)
      invariant |merged| == i + j
    {
      if i < |left| && (j == |right| || left[i] <= right[j]) then
        merged := merged + [left[i]];
        i := i + 1;
      else if j < |right| && (i == |left| || right[j] < left[i]) then
        merged := merged + [right[j]];
        j := j + 1;
      else
        // This case should not be reached if conditions are correctly managed
        assert false;
    }
    
    return merged;
}
// </vc-code>

