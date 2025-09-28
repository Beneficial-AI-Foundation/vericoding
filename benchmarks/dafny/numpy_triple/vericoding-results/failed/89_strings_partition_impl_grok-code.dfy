// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by removing named returns and using destructuring in ensures */
function SplitFirst(s: seq<char>, sep: seq<char>): (seq<char>, seq<char>, seq<char>)
  ensures var (before, sep_found, after) := SplitFirst(s, sep);
    |s| == |before| + |sep_found| + |after| &&
    s == before + sep_found + after &&
    sep_found == sep || sep_found == "" &&
    (sep_found == "" ==> after == "" && before == s) &&
    (sep_found == sep ==> |before| + |sep| <= |s| && s[|before|..|before| + |sep|] == sep && (forall k :: 0 <= k < |before| && k + |sep| <= |s| ==> s[k..k + |sep|] != sep) && after == s[|before| + |sep|..])
{
  if |sep| == 0 || |s| < |sep| then
    (s, [], [])
  else if s[..|sep|] == sep then
    ([], sep, s[|sep|..])
  else
    var (b, sf, af) := SplitFirst(s[1..], sep);
    ([s[0]] + b, sf, af)
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
/* code modified by LLM (iteration 5): Implemented method body using the updated helper function */
{
  var before_list := [];
  var sep_list := [];
  var after_list := [];
  for i := 0 to |a| - 1
  {
    var bf, sf, af := SplitFirst(a[i], sep);
    before_list := before_list + [bf];
    sep_list := sep_list + [sf];
    after_list := after_list + [af];
  }
  before := before_list;
  separator := sep_list;
  after := after_list;
}
// </vc-code>
