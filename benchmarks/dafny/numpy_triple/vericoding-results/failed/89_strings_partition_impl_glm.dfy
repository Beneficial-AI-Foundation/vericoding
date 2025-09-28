// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added explicit triggers to quantifiers and fixed loop invariants */
method FindFirstIndex(s: string, sep: string) returns (index: int)
  requires |sep| > 0
  ensures 0 <= index <= |s|
  ensures index == |s| ==> forall k {:trigger s[k..k + |sep|]} :: 0 <= k < |s| && k + |sep| <= |s| ==> s[k..k + |sep|] != sep
  ensures index < |s| ==> index + |sep| <= |s| && s[index..index + |sep|] == sep
  ensures forall k {:trigger s[k..k + |sep|]} :: 0 <= k < index && k + |sep| <= |s| ==> s[k..k + |sep|] != sep
{
  var i := 0;
  while i < |s| - |sep| + 1
    invariant 0 <= i <= |s| - |sep| + 1
    invariant forall k {:trigger s[k..k + |sep|]} :: 0 <= k < i && k + |sep| <= |s| ==> s[k..k + |sep|] != sep
  {
    if i + |sep| <= |s| && s[i..i + |sep|] == sep {
      return i;
    }
    i := i + 1;
  }
  return |s|;
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
  /* code modified by LLM (iteration 5): fixed loop invariant and quantifier triggers */
  before := [];
  separator := [];
  after := [];
  
  for i := 0 to |a|
    invariant |before| == i && |separator| == i && |after| == i
    invariant forall j :: 0 <= j < i ==> 
      before[j] + separator[j] + after[j] == a[j] &&
      (separator[j] == sep || separator[j] == "") &&
      (separator[j] == "" ==> after[j] == "" && before[j] == a[j]) &&
      (separator[j] == sep ==> 
        |before[j]| + |sep| <= |a[j]| &&
        a[j][|before[j]|..|before[j]| + |sep|] == sep &&
        (forall k {:trigger a[j][k..k + |sep|]} :: 0 <= k < |before[j]| && k + |sep| <= |a[j]| ==> 
          a[j][k..k + |sep|] != sep)) &&
      |a[j]| == |before[j]| + |separator[j]| + |after[j]| &&
      (separator[j] == sep ==> 
        after[j] == a[j][|before[j]| + |sep|..])
  {
    if sep == "" {
      before := before + [a[i]];
      separator := separator + [""];
      after := after + [""];
    } else {
      var idx := FindFirstIndex(a[i], sep);
      if idx < |a[i]| {
        before := before + [a[i][0..idx]];
        separator := separator + [sep];
        after := after + [a[i][idx + |sep|..]];
      } else {
        before := before + [a[i]];
        separator := separator + [""];
        after := after + [""];
      }
    }
  }
}
// </vc-code>
