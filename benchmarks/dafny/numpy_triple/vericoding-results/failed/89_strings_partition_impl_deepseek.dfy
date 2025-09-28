// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method FindSeparator(s: string, sep: string) returns (idx: nat, found: bool) 
  requires |sep| > 0
  ensures 0 <= idx <= |s|
  ensures found ==> idx + |sep| <= |s| && s[idx..idx + |sep|] == sep
  ensures found ==> (forall k :: 0 <= k < idx && k + |sep| <= |s| ==> s[k..k + |sep|] != sep)
  ensures !found ==> (forall k :: 0 <= k <= |s| - |sep| ==> s[k..k + |sep|] != sep)
{
  /* helper modified by LLM (iteration 5): Added decreases clause and fixed loop invariants */
  idx := 0;
  found := false;
  while idx <= |s| - |sep| && !found
    decreases |s| - |sep| - idx
    invariant 0 <= idx <= |s| - |sep| + 1
    invariant !found ==> (forall k :: 0 <= k < idx && k + |sep| <= |s| ==> s[k..k + |sep|] != sep)
  {
    if s[idx..idx + |sep|] == sep {
      found := true;
    } else {
      idx := idx + 1;
    }
  }
  if found {
    assert idx + |sep| <= |s|;
    assert s[idx..idx + |sep|] == sep;
  }
}
// </vc-helpers>

// <vc-spec>
method Partition(a: seq<string>, sep: string) returns (before: seq<string>, separator: seq<string>, after: seq<string>)
  // All result sequences have the same length as input
  ensures |before| == |a| && |separator| == |a| && |after| == |a|
  
  // Completeness: concatenation reconstructs original string
  ensures forall i :: 0 <= i < |a| ==> 
    before[i] + separator[i] + after[i] == a[i]
    
  // Separator correctness: either the actual separator or empty string
  ensures forall i :: 0 <= i < |a| ==> 
    separator[i] == sep || separator[i] == ""
    
  // Case when separator not found: before contains whole string, others empty
  ensures forall i :: 0 <= i < |a| ==> 
    (separator[i] == "" ==> after[i] == "" && before[i] == a[i])
    
  // First occurrence property: when separator is found, it's at the first valid position
  ensures forall i :: 0 <= i < |a| ==> 
    (separator[i] == sep ==> 
      |before[i]| + |sep| <= |a[i]| &&
      a[i][|before[i]|..|before[i]| + |sep|] == sep &&
      (forall k {:trigger a[i][k..k + |sep|]} :: 0 <= k < |before[i]| && k + |sep| <= |a[i]| ==> 
        a[i][k..k + |sep|] != sep))
        
  // Length preservation property
  ensures forall i :: 0 <= i < |a| ==> 
    |a[i]| == |before[i]| + |separator[i]| + |after[i]|
    
  // When separator found, after part starts immediately after separator
  ensures forall i :: 0 <= i < |a| ==> 
    (separator[i] == sep ==> 
      after[i] == a[i][|before[i]| + |sep|..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed FindSeparator precondition handling and loop invariants */
  before := [];
  separator := [];
  after := [];
  var i: int := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |before| == i && |separator| == i && |after| == i
    invariant forall j :: 0 <= j < i ==> 
      before[j] + separator[j] + after[j] == a[j] &&
      (separator[j] == sep || separator[j] == "") &&
      (separator[j] == "" ==> after[j] == "" && before[j] == a[j]) &&
      |a[j]| == |before[j]| + |separator[j]| + |after[j]| &&
      (separator[j] == sep ==> 
        |before[j]| + |sep| <= |a[j]| &&
        a[j][|before[j]|..|before[j]| + |sep|] == sep &&
        (forall k :: 0 <= k < |before[j]| && k + |sep| <= |a[j]| ==> 
          a[j][k..k + |sep|] != sep) &&
        after[j] == a[j][|before[j]| + |sep|..])
  {
    var s := a[i];
    var idx: nat, found: bool;
    if |s| >= |sep| && |sep| > 0 {
      idx, found := FindSeparator(s, sep);
    } else {
      idx := 0;
      found := false;
    }
    if found {
      before := before + [s[..idx]];
      separator := separator + [sep];
      after := after + [s[idx + |sep|..]];
    } else {
      before := before + [s];
      separator := separator + [""];
      after := after + [""];
    }
    i := i + 1;
  }
}
// </vc-code>
