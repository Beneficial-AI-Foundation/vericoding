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
/* helper modified by LLM (iteration 2): [named return value in Find to fix compilation error] */
function {:timeLimitMultiplier 2} Find(s: string, sub: string, start: nat): (res: nat)
  requires 0 <= start <= |s|
  requires sub != ""
  ensures start <= res <= |s|
  ensures res == |s| || (s[res..res+|sub|] == sub && forall i :: start <= i < res ==> s[i..i+|sub|] != sub)
{
  if start + |sub| > |s| then |s|
  else if s[start..start+|sub|] == sub then start
  else Find(s, sub, start + 1)
}

function {:timeLimitMultiplier 3} SplitString(s: string, sep: string, maxsplit: MaxSplit): (parts: seq<string>)
  requires sep != ""
  ensures |parts| >= 1
  ensures forall part :: part in parts ==> part != sep
  ensures s == "" ==> parts == [""]
  ensures s == sep ==> parts == ["", ""]
  ensures match maxsplit {
    case NoLimit => true
    case Limit(limit) => |parts| <= limit + 1
  }
  ensures Join(parts, sep) == s
  decreases |s|
{
  match maxsplit {
    case Limit(0) =>
      [s]
    case _ =>
      var idx := Find(s, sep, 0);
      if idx == |s| then
        [s]
      else
        var p := s[..idx];
        var s_prime := s[idx + |sep|..];
        var next_maxsplit := match maxsplit {
          case NoLimit => NoLimit
          case Limit(v) => Limit(v - 1)
        };
        [p] + SplitString(s_prime, sep, next_maxsplit)
  }
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
  /* code modified by LLM (iteration 2): [code unchanged, fix was in helper function] */
  var res: seq<seq<string>> := [];
  var i: nat := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == SplitString(a[j], sep, maxsplit)
  {
    var p := SplitString(a[i], sep, maxsplit);
    res := res + [p];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
