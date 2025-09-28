// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple predicate to describe an occurrence of sep at index i */
predicate OccursAt(s: string, sep: string, i: int)
{
  0 <= i && i + |sep| <= |s| && s[i..i + |sep|] == sep
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
  /* code modified by LLM (iteration 5): Implement explicit scan per string to ensure first-occurrence properties */
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
    invariant forall j :: 0 <= j < i ==> (separator[j] == "" ==> after[j] == "" && before[j] == a[j])
    invariant forall j :: 0 <= j < i ==> (separator[j] == sep ==> (|before[j]| + |sep| <= |a[j]| && a[j][|before[j]|..|before[j]| + |sep|] == sep && (forall k {:trigger a[j][k..k + |sep|]} :: 0 <= k < |before[j]| && k + |sep| <= |a[j]| ==> a[j][k..k + |sep|] != sep)))
    invariant forall j :: 0 <= j < i ==> |a[j]| == |before[j]| + |separator[j]| + |after[j]|
    invariant forall j :: 0 <= j < i ==> (separator[j] == sep ==> after[j] == a[j][|before[j]| + |sep|..])
    decreases n - i
  {
    var s := a[i];
    var m := |sep|;
    var b: string;
    var mstr: string;
    var c: string;

    if m == 0 {
      // Empty separator: occurs at position 0
      b := "";
      mstr := sep;
      c := s;
    } else {
      var j := 0;
      var found := false;
      var idx := 0;
      while j + m <= |s| && !found
        invariant 0 <= j <= |s|
        invariant 0 <= m
        invariant forall k {:trigger s[k..k + m]} :: 0 <= k < j && k + m <= |s| ==> s[k..k + m] != sep
        invariant found ==> (0 <= idx && idx + m <= |s| && s[idx..idx + m] == sep && j == idx)
        decreases |s| - j
      {
        if s[j..j + m] == sep {
          found := true;
          idx := j;
        } else {
          // help preserve the invariant for the next j
          assert s[j..j + m] != sep;
          j := j + 1;
        }
      }

      if found {
        // From invariants, j == idx and sep occurs at idx, and no earlier occurrence
        b := s[..idx];
        mstr := sep;
        c := s[idx + m..];
        // Establish the first-occurrence property for this element
        assert forall k {:trigger s[k..k + m]} :: 0 <= k < |b| && k + m <= |s| ==> s[k..k + m] != sep by {
          // since |b| == idx and invariant gives the property for all k < j, with j == idx
        }
      } else {
        // No occurrence found anywhere
        b := s;
        mstr := "";
        c := "";
      }
    }

    // Append results for this element
    before := before + [b];
    separator := separator + [mstr];
    after := after + [c];

    // Facts to maintain outer invariants
    assert b + mstr + c == s;
    assert mstr == sep || mstr == "";
    assert mstr == "" ==> (c == "" && b == s);
    assert |s| == |b| + |mstr| + |c|;
    assert mstr == sep ==> |b| + |sep| <= |s|;
    assert mstr == sep ==> s[|b|..|b| + |sep|] == sep;
    assert mstr == sep ==> (forall k {:trigger s[k..k + |sep|]} :: 0 <= k < |b| && k + |sep| <= |s| ==> s[k..k + |sep|] != sep);
    assert mstr == sep ==> c == s[|b| + |sep|..];

    i := i + 1;
  }
}

// </vc-code>
