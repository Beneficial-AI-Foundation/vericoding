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
/**/
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
/* code modified by LLM (iteration 5): Fixed compilation errors related to `var parts: seq<string>> := [];` by removing the extra `>`. Also fixed a parsing error in the `match` statement where `case Limit(limit) => { if limit == 0 then limitReached := true; }` was missing a '}' for the case body and the `if` statement wasn't a block. The previous iteration made an invalid change to the `match` syntax which is now corrected. */
{
  var res: seq<seq<string>> := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
  {
    var original := a[i];
    var parts: seq<string> := [];
    var currentSplitCount := 0;
    var currentIndex := 0;

    if original == "" {
      parts := [""];
    } else if original == sep {
      parts := ["", ""];
    } else {
      var limitReached := false;
      match maxsplit
        case Limit(limit) => {
          if limit == 0 {
            limitReached := true;
          }
        }
        case NoLimit => {}

      if limitReached {
          parts := [original];
      } else {
          while currentIndex < |original|
            invariant 0 <= currentIndex <= |original|
            invariant currentSplitCount >= 0
            invariant forall part :: part in parts[..] ==> part != sep
            invariant (exists limit_val :: maxsplit == Limit(limit_val) ==> currentSplitCount <= limit_val)
            decreases |original| - currentIndex
          {
            var nextSepIndex := currentIndex;
            var foundSep := false;

            while nextSepIndex + |sep| <= |original|
              invariant currentIndex <= nextSepIndex <= |original| - |sep|
              invariant forall k :: currentIndex <= k < nextSepIndex ==> !original[k .. k + |sep|] == sep
              decreases |original| - nextSepIndex
            {
              if original[nextSepIndex .. nextSepIndex + |sep|] == sep {
                foundSep := true;
                break;
              }
              nextSepIndex := nextSepIndex + 1;
            }

            var applyLimit := false;
            match maxsplit
              case NoLimit => applyLimit := false;
              case Limit(limit) => 
                if currentSplitCount == limit {
                  applyLimit := true;
                }

            if foundSep && !applyLimit {
              parts := parts + [original[currentIndex .. nextSepIndex]];
              currentIndex := nextSepIndex + |sep|;
              currentSplitCount := currentSplitCount + 1;
            } else {
              parts := parts + [original[currentIndex ..]];
              currentIndex := |original|;
            }
          }
      }
    }
    res := res + [parts];
  }
  result := res;
}
// </vc-code>
