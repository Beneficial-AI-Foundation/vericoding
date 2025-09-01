method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
method insert(sorted: seq<int>, x: int) returns (result: seq<int>)
  requires forall i,j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i,j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures |result| == |sorted| + 1
  ensures multiset(result) == multiset(sorted + [x])
{
  if |sorted| == 0 {
    result := [x];
    // multiset([x]) == multiset([] + [x])
  } 
  else if x <= sorted[0] {
    result := [x] + sorted;
    // x <= sorted[0], and sorted sorted, so result sorted
    // multiset([x] + sorted) == multiset(sorted + [x])
  }
  else {
    var tail := sorted[1..];
    var ins := insert(tail, x);
    // ins is sorted and multiset(ins) == multiset(tail + [x])
    
    // prove sortedness of [sorted[0]] + ins
    assert sorted[0] <= sorted[1] by { if |sorted| > 1 { } }
    if x <= sorted[1] {
      // ins starts with x, since x <= tail[0]
      assert ins[0] == x;
      assert sorted[0] <= x by { assert x > sorted[0]; assert x == ins[0]; }
    } else {
      // ins starts with sorted[1], since x > tail[0]
      if |tail| > 0 {
        assert ins[0] == tail[0] == sorted[1];
        assert sorted[0] <= sorted[1] == ins[0];
      }
    }
    assert forall k :: 0 <= k < |ins| ==> sorted[0] <= ins[k]; // due to above
    
    result := [sorted[0]] + ins;
    
    // prove multiset
    ghost var ms1 := multiset(sorted[1..] + [x]);
    ghost var ms2 := multiset(sorted);
    ghost var ms3 := multiset(sorted[0..1] + sorted[1..]);
    ghost var ms4 := multiset([sorted[0]] + ins);
    // ms3 == ms2, ms4 == multiset([sorted[0]]) + multiset(ins) == {sorted[0]} + multiset(sorted[1..] + [x]) == {sorted[0]} + ms1
    // multiset(sorted + [x]) = multiset(sorted) + {x} = ms2 + {x}
    // ms4 = {sorted[0]} + (multiset(sorted[1..]) + {x}) = multiset(sorted[1..]) + {sorted[0]} + {x} = multiset(sorted[1..]) + {sorted[0]} + {x}
    // ms2 = multiset(sorted[0..1]) * count + multiset(sorted[1..])
    // but since count of sorted[0] is 1, and {sorted[0]} + multiset(sorted[1..]) == ms2
    // so ms2 + {x} == {sorted[0]} + multiset(sorted[1..]) + {x} == ms4
    assert multiset(result) == ms4 == ms2 + multiset([x]);
  }
}
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
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant forall j,k :: 0 <= j < k < |sorted| ==> sorted[j] <= sorted[k]
    invariant multiset(sorted) == multiset(s[..i])
  {
    var temp := insert(sorted, s[i]);
    assert multiset(temp) == multiset(sorted + [s[i]]);
    assert multiset(s[..i] + [s[i]]) == multiset(s[..i+1]);
    // from insert ensures and assumes
    sorted := temp;
    i := i + 1;
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
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// pure-end