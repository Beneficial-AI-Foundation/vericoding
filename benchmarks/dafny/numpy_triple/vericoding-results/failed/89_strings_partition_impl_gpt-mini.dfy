// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): FirstIndexFrom implemented with explicit recursive proof and FirstIndex wrapper */
function FirstIndexFrom(s: string, sep: string, k: int): int
  requires sep != ""
  requires 0 <= k <= |s|
  ensures k <= FirstIndexFrom(s,sep,k) <= |s|
  ensures (FirstIndexFrom(s,sep,k) < |s| ==> FirstIndexFrom(s,sep,k) + |sep| <= |s| && s[FirstIndexFrom(s,sep,k)..FirstIndexFrom(s,sep,k)+|sep|] == sep)
  ensures forall j {:trigger s[j..j+|sep|]} :: k <= j < FirstIndexFrom(s,sep,k) && j + |sep| <= |s| ==> s[j..j+|sep|] != sep
  decreases |s| - k
{
  if k + |sep| > |s| then |s|
  else if s[k..k+|sep|] == sep then k
  else
    var r := FirstIndexFrom(s, sep, k+1);
    // From recursive call we have k+1 <= r <= |s| and the forall for j in [k+1, r)
    assert k <= r;
    assert s[k..k+|sep|] != sep;
    assert forall j {:trigger s[j..j+|sep|]} :: k+1 <= j < r && j + |sep| <= |s| ==> s[j..j+|sep|] != sep;
    // Combine the base non-match at k with the recursive property to get the required range
    assert forall j {:trigger s[j..j+|sep|]} :: k <= j < r && j + |sep| <= |s| ==> s[j..j+|sep|] != sep;
    r
}

/* helper modified by LLM (iteration 5): FirstIndex wrapper using FirstIndexFrom */
function FirstIndex(s: string, sep: string): int
  requires sep != ""
  ensures 0 <= FirstIndex(s, sep) <= |s|
  ensures (FirstIndex(s, sep) < |s| ==> FirstIndex(s, sep) + |sep| <= |s| && s[FirstIndex(s, sep) .. FirstIndex(s, sep) + |sep|] == sep)
  ensures forall k {:trigger s[k..k+|sep|]} :: 0 <= k < FirstIndex(s, sep) && k + |sep| <= |s| ==> s[k..k+|sep|] != sep
  decreases |s|
{
  FirstIndexFrom(s, sep, 0)
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
  /* code modified by LLM (iteration 5): implement partition using FirstIndex and explicit asserts to establish invariants */
  var n := |a|;
  before := [];
  separator := [];
  after := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |before| == i && |separator| == i && |after| == i
    invariant forall j :: 0 <= j < i ==> before[j] + separator[j] + after[j] == a[j]
    invariant forall j :: 0 <= j < i ==> separator[j] == sep || separator[j] == ""
    invariant forall j :: 0 <= j < i ==> |a[j]| == |before[j]| + |separator[j]| + |after[j]|
    invariant forall j :: 0 <= j < i ==> (separator[j] == "" ==> after[j] == "" && before[j] == a[j])
    invariant forall j :: 0 <= j < i ==> (separator[j] == sep ==> |before[j]| + |sep| <= |a[j]| && a[j][|before[j]|..|before[j]| + |sep|] == sep && (forall k :: 0 <= k < |before[j]| && k + |sep| <= |a[j]| ==> a[j][k..k + |sep|] != sep))
    invariant forall j :: 0 <= j < i ==> (separator[j] == sep ==> after[j] == a[j][|before[j]| + |sep|..])
    decreases n - i
  {
    var s := a[i];
    if sep == "" {
      before := before + [s];
      separator := separator + [""];
      after := after + [""];
    } else {
      var idx := FirstIndex(s, sep);
      if idx >= |s| {
        before := before + [s];
        separator := separator + [""];
        after := after + [""];
      } else {
        // Use properties from FirstIndex to discharge invariants for the new element
        assert idx + |sep| <= |s|;
        assert s[idx..idx+|sep|] == sep;
        assert forall k {:trigger s[k..k+|sep|]} :: 0 <= k < idx && k + |sep| <= |s| ==> s[k..k+|sep|] != sep;
        var b := s[..idx];
        var sepPart := s[idx..idx+|sep|];
        var aPart := s[idx+|sep|..];
        before := before + [b];
        separator := separator + [sepPart];
        after := after + [aPart];
      }
    }
    i := i + 1;
  }
}

// </vc-code>
