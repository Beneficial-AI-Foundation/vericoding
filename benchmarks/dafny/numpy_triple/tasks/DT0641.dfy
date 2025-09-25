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
  assume {:axiom} false;
}
// </vc-code>
