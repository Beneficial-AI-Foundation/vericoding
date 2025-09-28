// <vc-preamble>
// Helper function to join strings with a separator
function Join(parts: seq<string>, sep: string): string
{
    if |parts| == 0 then ""
    else if |parts| == 1 then parts[0]
    else parts[0] + sep + Join(parts[1..], sep)
}

// Datatype to represent optional maximum split limit
datatype MaxSplit = NoLimit | Limit(value: nat)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed verification issues in helper functions */
function SplitString(s: string, sep: string, maxsplit: MaxSplit): seq<string>
  requires sep != ""
  ensures |SplitString(s, sep, maxsplit)| >= 1
  ensures s == "" ==> SplitString(s, sep, maxsplit) == [""]
  ensures s == sep ==> SplitString(s, sep, maxsplit) == ["", ""]
  ensures forall part :: part in SplitString(s, sep, maxsplit) ==> part != sep
  decreases |s|
{
  if s == "" then [""]
  else if s == sep then ["", ""]
  else if |s| < |sep| then [s]
  else SplitRecursive(s, sep, maxsplit, 0)
}

function SplitRecursive(s: string, sep: string, maxsplit: MaxSplit, splitsDone: nat): seq<string>
  requires sep != ""
  requires |s| >= |sep|
  ensures |SplitRecursive(s, sep, maxsplit, splitsDone)| >= 1
  ensures forall part :: part in SplitRecursive(s, sep, maxsplit, splitsDone) ==> part != sep
  decreases |s|
{
  if maxsplit.Limit? && splitsDone >= maxsplit.value then
    [s]
  else
    var idx := FindSeparator(s, sep, 0);
    if idx < 0 then
      [s]
    else
      var before := s[..idx];
      var afterIdx := idx + |sep|;
      if afterIdx >= |s| then
        [before, ""]
      else
        var after := s[afterIdx..];
        if |after| < |sep| then
          [before, after]
        else
          [before] + SplitRecursive(after, sep, maxsplit, splitsDone + 1)
}

function FindSeparator(s: string, sep: string, start: nat): int
  requires sep != ""
  requires start <= |s|
  ensures -1 <= FindSeparator(s, sep, start) < |s|
  ensures FindSeparator(s, sep, start) >= 0 ==> 
    FindSeparator(s, sep, start) + |sep| <= |s| &&
    s[FindSeparator(s, sep, start)..FindSeparator(s, sep, start) + |sep|] == sep
  decreases |s| - start
{
  if start > |s| - |sep| then
    -1
  else if start + |sep| <= |s| && s[start..start + |sep|] == sep then
    start
  else
    FindSeparator(s, sep, start + 1)
}
// </vc-helpers>

// <vc-spec>
method Split(a: seq<string>, sep: string, maxsplit: MaxSplit) returns (result: seq<seq<string>>)
    requires sep != ""
    requires |a| >= 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==>
        var parts := result[i];
        var original := a[i];
        // Basic correctness: none of the parts equal the separator
        (forall part :: part in parts ==> part != sep) &&
        // If maxsplit is specified, respect the limit
        (match maxsplit
            case NoLimit => true
            case Limit(limit) => |parts| <= limit + 1) &&
        // The result is non-empty (at least contains one element)
        |parts| >= 1 &&
        // If original is empty, return empty string as single element
        (original == "" ==> parts == [""]) &&
        // If original equals separator, return two empty parts
        (original == sep ==> parts == ["", ""]) &&
        // The parts when joined with separator should reconstruct the original (up to maxsplit)
        (match maxsplit
            case NoLimit => Join(parts, sep) == original
            case Limit(limit) => 
                if |parts| <= limit + 1 then
                    Join(parts, sep) == original
                else
                    // When maxsplit is reached, last part contains remaining string
                    |parts| == limit + 1 && 
                    Join(parts[..limit], sep) + sep + parts[limit] == original)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Simplified implementation using SplitString */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      var parts := result[j];
      var original := a[j];
      (forall part :: part in parts ==> part != sep) &&
      (match maxsplit
        case NoLimit => true
        case Limit(limit) => |parts| <= limit + 1) &&
      |parts| >= 1 &&
      (original == "" ==> parts == [""]) &&
      (original == sep ==> parts == ["", ""])
  {
    var parts := SplitString(a[i], sep, maxsplit);
    result := result + [parts];
    i := i + 1;
  }
}
// </vc-code>
