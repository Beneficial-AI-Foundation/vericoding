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
/* helper modified by LLM (iteration 5): Fixed FindNextSep return type and verification properties */
function FindNextSep(s: string, sep: string, start: int): (found: bool, pos: int)
  requires sep != ""
  requires 0 <= start <= |s|
  decreases |s| - start
  ensures found ==> start <= pos <= |s| - |sep| && s[pos..pos+|sep|] == sep
  ensures !found ==> forall j | start <= j < |s| - |sep| + 1 :: s[j..j+|sep|] != sep
{
  if start > |s| - |sep| then
    (false, 0)
  else if s[start..start+|sep|] == sep then
    (true, start)
  else
    FindNextSep(s, sep, start+1)
}

predicate RespectsMaxSplit(parts: seq<string>, maxsplit: MaxSplit)
{
  match maxsplit
    case NoLimit => true
    case Limit(limit) => |parts| <= limit + 1
}

predicate ValidSplit(original: string, parts: seq<string>, sep: string, maxsplit: MaxSplit)
  requires sep != ""
{
  |parts| >= 1 &&
  (original == "" ==> parts == [""]) &&
  (original == sep ==> parts == ["", ""]) &&
  (forall part :: part in parts ==> part != sep) &&
  RespectsMaxSplit(parts, maxsplit) &&
  (match maxsplit
    case NoLimit => Join(parts, sep) == original
    case Limit(limit) => 
      if |parts| <= limit + 1 then
        Join(parts, sep) == original
      else
        |parts| == limit + 1 && 
        Join(parts[..limit], sep) + sep + parts[limit] == original)
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
  /* code modified by LLM (iteration 5): Fixed compilation error with FindNextSep return type */
  result := new string[|a|][];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == |a|
    invariant forall j :: 0 <= j < i ==> ValidSplit(a[j], result[j], sep, maxsplit)
  {
    var s := a[i];
    if s == "" {
      result[i] := [""];
    } else if s == sep {
      result[i] := ["", ""];
    } else {
      var parts: seq<string> := [];
      var start := 0;
      var split_count := 0;
      var max_splits := match maxsplit {
        case Limit(limit) => limit
        case NoLimit => |s| + 1
      };

      while start < |s| && split_count < max_splits
        invariant 0 <= start <= |s|
        invariant 0 <= split_count <= max_splits
        invariant forall part :: part in parts ==> part != sep
        invariant |parts| == split_count
        invariant start == 0 || split_count > 0
      {
        var (found, pos) := FindNextSep(s, sep, start);
        if found {
          parts := parts + [s[start..pos]];
          start := pos + |sep|;
          split_count := split_count + 1;
        } else {
          break;
        }
      }
      
      if start <= |s| {
        parts := parts + [s[start..]];
      }
      
      result[i] := parts;
    }
    i := i + 1;
  }
}
// </vc-code>
