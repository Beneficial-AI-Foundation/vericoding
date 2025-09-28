// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Find(s: string, sub: string): nat
  requires |sub| > 0
  ensures 0 <= Find(s, sub) <= |s|
  ensures Find(s, sub) < |s| ==> Find(s, sub) + |sub| <= |s| && s[Find(s,sub)..Find(s,sub)+|sub|] == sub
  ensures Find(s, sub) < |s| ==> forall k :: 0 <= k < Find(s, sub) && k + |sub| <= |s| ==> s[k..k+|sub|] != sub
  ensures Find(s, sub) == |s| ==> forall k :: 0 <= k <= |s| - |sub| ==> s[k..k+|sub|] != sub
{
  if |s| < |sub| then |s|
  else if s[0..|sub|] == sub then 0
  else
    var rest_pos := Find(s[1..], sub);
    if rest_pos == |s[1..]| then |s| else 1 + rest_pos
}

/* helper modified by LLM (iteration 5): [named return values in PartitionString to fix compilation errors] */
function PartitionString(s: string, sep: string) returns (before: string, separator: string, after: string)
  requires |sep| > 0
  ensures before + separator + after == s
  ensures separator == sep || separator == ""
  ensures separator == "" ==> after == "" && before == s
  ensures separator == sep ==>
    |before| + |sep| <= |s| &&
    s[|before|..|before| + |sep|] == sep &&
    (forall k {:trigger s[k..k + |sep|]} :: 0 <= k < |before| && k + |sep| <= |s| ==> 
      s[k..k + |sep|] != sep)
  ensures |s| == |before| + |separator| + |after|
  ensures separator == sep ==> after == s[|before| + |sep|..]
{
  var pos := Find(s, sep);
  if pos == |s| then
    (s, "", "")
  else
    (s[..pos], sep, s[pos+|sep|..])
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
  /* code modified by LLM (iteration 5): [use named tuple access to match helper and handle empty separator] */
  if sep == "" {
    before := seq(|a|, i => a[i]);
    separator := seq(|a|, i => "");
    after := seq(|a|, i => "");
  } else {
    var results := seq(|a|, i => PartitionString(a[i], sep));
    before := seq(|a|, i => results[i].before);
    separator := seq(|a|, i => results[i].separator);
    after := seq(|a|, i => results[i].after);
  }
}
// </vc-code>
