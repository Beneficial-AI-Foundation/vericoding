// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed redundant assertions and fixed postcondition verification */
function FindSeparator(s: string, sep: string): int
  ensures var pos := FindSeparator(s, sep);
    pos == -1 || (0 <= pos && pos + |sep| <= |s|)
  ensures var pos := FindSeparator(s, sep);
    pos >= 0 ==> s[pos..pos + |sep|] == sep
  ensures var pos := FindSeparator(s, sep);
    pos >= 0 ==> forall k :: 0 <= k < pos && k + |sep| <= |s| ==> s[k..k + |sep|] != sep
{
  if |sep| == 0 || |sep| > |s| then
    -1
  else
    FindSeparatorFrom(s, sep, 0)
}

function FindSeparatorFrom(s: string, sep: string, start: int): int
  requires 0 <= start <= |s|
  requires |sep| > 0
  decreases |s| - start
  ensures var pos := FindSeparatorFrom(s, sep, start);
    pos == -1 || (start <= pos && pos + |sep| <= |s|)
  ensures var pos := FindSeparatorFrom(s, sep, start);
    pos >= 0 ==> s[pos..pos + |sep|] == sep
  ensures var pos := FindSeparatorFrom(s, sep, start);
    pos >= 0 ==> forall k :: start <= k < pos && k + |sep| <= |s| ==> s[k..k + |sep|] != sep
  ensures var pos := FindSeparatorFrom(s, sep, start);
    pos == -1 ==> forall k :: start <= k && k + |sep| <= |s| ==> s[k..k + |sep|] != sep
{
  if start + |sep| > |s| then
    -1
  else if s[start..start + |sep|] == sep then
    start
  else
    FindSeparatorFrom(s, sep, start + 1)
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
  /* code modified by LLM (iteration 5): Removed redundant assertions that are already guaranteed by function postconditions */
  var resultBefore := [];
  var resultSeparator := [];
  var resultAfter := [];
  
  for i := 0 to |a|
    invariant |resultBefore| == i
    invariant |resultSeparator| == i
    invariant |resultAfter| == i
    invariant forall j :: 0 <= j < i ==>
      resultBefore[j] + resultSeparator[j] + resultAfter[j] == a[j]
    invariant forall j :: 0 <= j < i ==>
      resultSeparator[j] == sep || resultSeparator[j] == ""
    invariant forall j :: 0 <= j < i ==>
      (resultSeparator[j] == "" ==> resultAfter[j] == "" && resultBefore[j] == a[j])
    invariant forall j :: 0 <= j < i ==>
      (resultSeparator[j] == sep ==>
        |resultBefore[j]| + |sep| <= |a[j]| &&
        a[j][|resultBefore[j]|..|resultBefore[j]| + |sep|] == sep &&
        (forall k {:trigger a[j][k..k + |sep|]} :: 0 <= k < |resultBefore[j]| && k + |sep| <= |a[j]| ==>
          a[j][k..k + |sep|] != sep))
    invariant forall j :: 0 <= j < i ==>
      |a[j]| == |resultBefore[j]| + |resultSeparator[j]| + |resultAfter[j]|
    invariant forall j :: 0 <= j < i ==>
      (resultSeparator[j] == sep ==>
        resultAfter[j] == a[j][|resultBefore[j]| + |sep|..])
  {
    var pos := FindSeparator(a[i], sep);
    if pos >= 0 {
      var bef := a[i][..pos];
      var aft := a[i][pos + |sep|..];
      
      resultBefore := resultBefore + [bef];
      resultSeparator := resultSeparator + [sep];
      resultAfter := resultAfter + [aft];
    } else {
      resultBefore := resultBefore + [a[i]];
      resultSeparator := resultSeparator + [""];
      resultAfter := resultAfter + [""];
    }
  }
  
  before := resultBefore;
  separator := resultSeparator;
  after := resultAfter;
}
// </vc-code>
