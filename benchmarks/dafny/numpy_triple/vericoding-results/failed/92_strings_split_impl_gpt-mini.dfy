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
/* helper modified by LLM (iteration 5): find first occurrence of sep starting from i */
function FindFirst(s: string, sep: string, i: nat): nat
  requires sep != ""
  requires i <= |s|
  decreases |s| - i
  ensures i <= result <= |s|
  ensures result < |s| ==> result + |sep| <= |s|
  ensures result < |s| ==> s[result..result + |sep|] == sep
  ensures forall j :: i <= j < result ==> (j + |sep| <= |s| ==> s[j..j + |sep|] != sep)
{
  if i + |sep| > |s| then
    |s|
  else if s[i..i + |sep|] == sep then
    i
  else
    FindFirst(s, sep, i + 1)
}

/* helper modified by LLM (iteration 5): split without a limit starting from index start */
function SplitNoLimit(s: string, sep: string, start: nat): seq<string>
  requires sep != ""
  requires start <= |s|
  decreases |s| - start
  ensures |result| >= 1
  ensures forall part :: part in result ==> part != sep
  ensures Join(result, sep) == s[start..]
  ensures s[start..] == "" ==> result == [""]
  ensures s[start..] == sep ==> result == ["", ""]
{
  if start == |s| then
    [""]
  else
    var n := FindFirst(s, sep, start);
    if n == |s| then
      [s[start..]]
    else
      [s[start..n]] + SplitNoLimit(s, sep, n + |sep|)
}

/* helper modified by LLM (iteration 5): split with a remaining split limit rem starting from index start */
function SplitLimit(s: string, sep: string, start: nat, rem: nat): seq<string>
  requires sep != ""
  requires start <= |s|
  decreases |s| - start, rem
  ensures |result| >= 1
  ensures forall part :: part in result ==> part != sep
  ensures (rem == 0 || start == |s|) ==> result == [s[start..]]
  ensures rem > 0 && start < |s| ==>
    (if result == [s[start..]] then true else
      (if |result| <= rem + 1 then Join(result, sep) == s[start..] else |result| == rem + 1 && Join(result[..rem], sep) + sep + result[rem] == s[start..]))
{
  if rem == 0 || start == |s| then
    [s[start..]]
  else
    var n := FindFirst(s, sep, start);
    if n == |s| then
      [s[start..]]
    else
      [s[start..n]] + SplitLimit(s, sep, n + |sep|, rem - 1)
}

/* helper modified by LLM (iteration 5): dispatch SplitString to limited or unlimited variant */
function SplitString(s: string, sep: string, max: MaxSplit): seq<string>
  requires sep != ""
  ensures |result| >= 1
  ensures forall part :: part in result ==> part != sep
  ensures s == "" ==> result == [""]
  ensures s == sep ==> result == ["", ""]
  ensures match max
            case NoLimit => Join(result, sep) == s
            case Limit(limit) =>
              if |result| <= limit + 1 then Join(result, sep) == s
              else |result| == limit + 1 && Join(result[..limit], sep) + sep + result[limit] == s
{
  match max
    case NoLimit => SplitNoLimit(s, sep, 0)
    case Limit(l) => SplitLimit(s, sep, 0, l)
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
  /* code modified by LLM (iteration 5): iterate over input seq and split each element, maintaining invariants about each produced parts */
  var res: seq<seq<string>> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall k :: 0 <= k < |res| ==>
      (forall part :: part in res[k] ==> part != sep) &&
      |res[k]| >= 1 &&
      (a[k] == "" ==> res[k] == [""]) &&
      (a[k] == sep ==> res[k] == ["", ""]) &&
      (match maxsplit
         case NoLimit => Join(res[k], sep) == a[k]
         case Limit(limit) =>
           if |res[k]| <= limit + 1 then Join(res[k], sep) == a[k]
           else |res[k]| == limit + 1 && Join(res[k][..limit], sep) + sep + res[k][limit] == a[k])
  {
    var parts := SplitString(a[i], sep, maxsplit);
    res := res + [parts];
    i := i + 1;
  }
  result := res;
}

// </vc-code>
