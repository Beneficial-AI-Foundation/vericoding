// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed postcondition proofs and empty separator handling */
function FindFirstOccurrence(s: string, sep: string): int
  ensures FindFirstOccurrence(s, sep) == -1 <==> (forall k {:trigger s[k..k + |sep|]} :: 0 <= k < |s| && k + |sep| <= |s| ==> s[k..k + |sep|] != sep)
  ensures FindFirstOccurrence(s, sep) >= 0 ==> 
    FindFirstOccurrence(s, sep) + |sep| <= |s| &&
    s[FindFirstOccurrence(s, sep)..FindFirstOccurrence(s, sep) + |sep|] == sep &&
    (forall k {:trigger s[k..k + |sep|]} :: 0 <= k < FindFirstOccurrence(s, sep) && k + |sep| <= |s| ==> s[k..k + |sep|] != sep)
{
  if |sep| == 0 then (
    assert forall k {:trigger s[k..k]} :: 0 <= k < |s| && k <= |s| ==> s[k..k] == "" != sep;
    -1
  )
  else if |sep| > |s| then -1
  else
    FindFirstOccurrenceHelper(s, sep, 0)
}

function FindFirstOccurrenceHelper(s: string, sep: string, i: int): int
  requires 0 <= i <= |s|
  requires |sep| > 0 && |sep| <= |s|
  ensures FindFirstOccurrenceHelper(s, sep, i) == -1 <==> (forall k {:trigger s[k..k + |sep|]} :: i <= k < |s| && k + |sep| <= |s| ==> s[k..k + |sep|] != sep)
  ensures FindFirstOccurrenceHelper(s, sep, i) >= 0 ==> 
    i <= FindFirstOccurrenceHelper(s, sep, i) < |s| &&
    FindFirstOccurrenceHelper(s, sep, i) + |sep| <= |s| &&
    s[FindFirstOccurrenceHelper(s, sep, i)..FindFirstOccurrenceHelper(s, sep, i) + |sep|] == sep &&
    (forall k {:trigger s[k..k + |sep|]} :: i <= k < FindFirstOccurrenceHelper(s, sep, i) && k + |sep| <= |s| ==> s[k..k + |sep|] != sep)
  decreases |s| - i
{
  if i > |s| - |sep| then (
    assert forall k {:trigger s[k..k + |sep|]} :: i <= k < |s| && k + |sep| <= |s| ==> false;
    -1
  )
  else if s[i..i + |sep|] == sep then (
    assert s[i..i + |sep|] == sep;
    assert forall k {:trigger s[k..k + |sep|]} :: i <= k < i && k + |sep| <= |s| ==> false;
    i
  )
  else (
    var rest := FindFirstOccurrenceHelper(s, sep, i + 1);
    assert s[i..i + |sep|] != sep;
    rest
  )
}

lemma EmptySeqSliceProperty(s: string, sep: string)
  requires |sep| == 0
  ensures forall k {:trigger s[k..k]} :: 0 <= k < |s| && k + |sep| <= |s| ==> s[k..k + |sep|] != sep
{
  assert |sep| == 0;
  assert sep == "";
  forall k | 0 <= k < |s| && k + |sep| <= |s|
    ensures s[k..k + |sep|] != sep
  {
    assert s[k..k + |sep|] == s[k..k] == "";
    assert "" != sep by {
      assert |sep| == 0;
      assert sep != "" || |sep| > 0;
    }
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
  /* code modified by LLM (iteration 5): simplified empty sep handling and added assertions for postconditions */
  before := [];
  separator := [];
  after := [];
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |before| == i && |separator| == i && |after| == i
    invariant forall j {:trigger before[j] + separator[j] + after[j]} :: 0 <= j < i ==> before[j] + separator[j] + after[j] == a[j]
    invariant forall j :: 0 <= j < i ==> separator[j] == sep || separator[j] == ""
    invariant forall j :: 0 <= j < i ==> (separator[j] == "" ==> after[j] == "" && before[j] == a[j])
    invariant forall j :: 0 <= j < i ==> |a[j]| == |before[j]| + |separator[j]| + |after[j]|
    invariant forall j :: 0 <= j < i ==> 
      (separator[j] == sep ==> 
        |before[j]| + |sep| <= |a[j]| &&
        a[j][|before[j]|..|before[j]| + |sep|] == sep &&
        (forall k {:trigger a[j][k..k + |sep|]} :: 0 <= k < |before[j]| && k + |sep| <= |a[j]| ==> a[j][k..k + |sep|] != sep))
    invariant forall j :: 0 <= j < i ==> 
      (separator[j] == sep ==> after[j] == a[j][|before[j]| + |sep|..])
  {
    if |sep| == 0 {
      EmptySeqSliceProperty(a[i], sep);
      before := before + [a[i]];
      separator := separator + [""]; 
      after := after + [""]; 
      assert before[i] + separator[i] + after[i] == a[i] + "" + "" == a[i];
    } else {
      var pos := FindFirstOccurrence(a[i], sep);
      
      if pos == -1 {
        before := before + [a[i]];
        separator := separator + [""]; 
        after := after + [""]; 
        assert before[i] + separator[i] + after[i] == a[i] + "" + "" == a[i];
      } else {
        assert pos >= 0;
        assert pos + |sep| <= |a[i]|;
        var beforeStr := a[i][..pos];
        var afterStr := a[i][pos + |sep|..];
        before := before + [beforeStr];
        separator := separator + [sep];
        after := after + [afterStr];
        
        assert a[i][pos..pos + |sep|] == sep;
        assert |beforeStr| == pos;
        assert beforeStr + sep + afterStr == a[i][..pos] + a[i][pos..pos + |sep|] + a[i][pos + |sep|..] == a[i];
      }
    }
    
    i := i + 1;
  }
}
// </vc-code>
