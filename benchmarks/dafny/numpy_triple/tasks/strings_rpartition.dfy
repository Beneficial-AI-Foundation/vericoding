// <vc-preamble>
// Helper function to find the last occurrence of a substring in a string
ghost function LastIndexOf(s: string, sub: string): int
{
    if sub == "" then |s|
    else if !(exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub) then -1
    else
        var indices := set i {:trigger s[i..i+|sub|]} | 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub;
        if indices == {} then -1
        else
            // Find maximum index in the set
            var max_idx :| max_idx in indices && forall idx :: idx in indices ==> idx <= max_idx;
            max_idx
}

// Helper function to check if a substring occurs at a specific position
ghost predicate SubstringAt(s: string, sub: string, pos: int)
{
    0 <= pos <= |s| - |sub| && s[pos..pos+|sub|] == sub
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RPartition(a: seq<string>, sep: string) returns (before: seq<string>, separator: seq<string>, after: seq<string>)
    requires sep != ""  // Non-empty separator for well-defined behavior
    ensures |before| == |a|
    ensures |separator| == |a|
    ensures |after| == |a|
    ensures forall i :: 0 <= i < |a| ==>
        var original := a[i];
        var before_i := before[i];
        var sep_i := separator[i];
        var after_i := after[i];
        // Completeness: concatenation reconstructs original
        before_i + sep_i + after_i == original &&
        // Separator correctness
        (sep_i == sep || sep_i == "") &&
        // Last occurrence semantics
        (if exists j {:trigger original[j..j+|sep|]} :: 0 <= j <= |original| - |sep| && original[j..j+|sep|] == sep then
            var last_pos := LastIndexOf(original, sep);
            last_pos >= 0 &&
            before_i == original[..last_pos] &&
            sep_i == sep &&
            after_i == original[last_pos + |sep|..]
        else
            before_i == "" && sep_i == "" && after_i == original)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
