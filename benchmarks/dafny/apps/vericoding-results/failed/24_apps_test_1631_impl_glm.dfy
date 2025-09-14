ghost predicate validInput(stdin_input: string, n: int)
{
    exists lines :: (parseInput(stdin_input) == lines &&
    |lines| >= 1 &&
    |lines| == n + 1 &&
    parseInt(lines[0]) == n &&
    n >= 1 && n <= 100 &&
    (forall i :: 1 <= i < |lines| ==> 
        1 <= |lines[i]| <= 100 && 
        forall j :: 0 <= j < |lines[i]| ==> 'a' <= lines[i][j] <= 'z'))
}

ghost predicate validAlphabetOrdering(stdin_input: string, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
{
    exists lines, n :: (parseInput(stdin_input) == lines &&
    |lines| >= 1 &&
    |lines| == n + 1 &&
    parseInt(lines[0]) == n &&
    (forall i :: 1 <= i < n ==> lexicographicallyLessOrEqual(lines[i], lines[i+1], alphabet)))
}

ghost predicate lexicographicallyLessOrEqual(s1: string, s2: string, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
{
    if s1 == s2 then
        true
    else if |s1| <= |s2| && s1 == s2[..|s1|] then
        true
    else if |s2| < |s1| && s2 == s1[..|s2|] then
        false
    else
        exists i :: (0 <= i < |s1| && i < |s2| && s1[i] != s2[i] &&
        (forall j :: 0 <= j < i ==> s1[j] == s2[j]) &&
        'a' <= s1[i] <= 'z' && 'a' <= s2[i] <= 'z' &&
        alphabetOrder(s1[i], s2[i], alphabet))
}

ghost predicate alphabetOrder(c1: char, c2: char, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    requires 'a' <= c1 <= 'z' && 'a' <= c2 <= 'z'
{
    exists i, j :: 0 <= i < j < |alphabet| && alphabet[i] == c1 && alphabet[j] == c2
}

ghost function parseInput(input: string): seq<string>

ghost function parseInt(s: string): int

// <vc-helpers>
function {:attestation 6}indexOf(dna: string, c: char): (index: int)
    requires 'a' <= c <= 'z'
    requires forall i :: 0 <= i < |dna| ==> 'a' <= dna[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |dna| ==> dna[i] != dna[j]
    ensures 0 <= index < |dna| && dna[index] == c
{
    if dna[0] == c then 0 else indexOf(dna[1..], c) + 1
}

function {:attestation 6}substring(s: string, start: int, len: int): string
    requires 0 <= start && 0 <= len && start + len <= |s|
    ensures |substring(s, start, len)| == len
    ensures forall j :: 0 <= j < len ==> substring(s, start, len)[j] == s[start+j]
{
    if len == 0 then "" else [s[start]] + substring(s, start+1, len-1)
}

function {:attestation 6}lexCompare(s1: string, s2: string, alphabet: string): int
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    ensures lexCompare(s1, s2, alphabet) < 0 <==> lexicographicallyLessOrEqual(s1, s2, alphabet) && s1 != s2
    ensures lexCompare(s1, s2, alphabet) == 0 <==> s1 == s2
    ensures lexCompare(s1, s2, alphabet) > 0 <==> !lexicographicallyLessOrEqual(s1, s2, alphabet)
{
    if s1 == s2 then 0
    else if |s1| <= |s2| && s1 == s2[..|s1|] then -1
    else if |s2| < |s1| && s2 == s1[..|s2|] then 1
    else
        var i :| 0 <= i < |s1| && i < |s2| && s1[i] != s2[i] && (forall j :: 0 <= j < i ==> s1[j] == s2[j]);
        var idx1 := indexOf(alphabet, s1[i]);
        var idx2 := indexOf(alphabet, s2[i]);
        if idx1 < idx2 then -1 else 1
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists n :: n >= 1 && validInput(stdin_input, n)
    ensures result == "Impossible" || (|result| == 26 && forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z')
    ensures result != "Impossible" ==> (forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j])
    ensures result != "Impossible" ==> validAlphabetOrdering(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var lines := parseInput(stdin_input);
    var n := parseInt(lines[0]);
    var alphabet := "abcdefghijklmnopqrstuvwxyz";
    
    if (forall i :: 1 <= i < n ==> lexCompare(lines[i], lines[i+1], alphabet) <= 0) {
        return alphabet;
    }
    
    var i, j: int, k: nat := 1, 0, 0;
    var found: bool := false;
    var prefix: string := "";
    var order: array<char> := new char[26];
    var used: array<bool> := new bool[26];
    
    for l := 0 to 26 {
        used[l] := false;
    }
    
    while i < n && !found {
        var s1 := lines[i];
        var s2 := lines[i+1];
        var min_len := if |s1| < |s2| then |s1| else |s2|;
        var diff_idx: int := -1;
        var l := 0;
        
        while l < min_len {
            if s1[l] != s2[l] {
                diff_idx := l;
                break;
            }
            l := l + 1;
        }
        
        if diff_idx != -1 {
            var c1 := s1[diff_idx];
            var c2 := s2[diff_idx];
            var idx1 := indexOf(alphabet, c1);
            var idx2 := indexOf(alphabet, c2);
            
            if idx1 > idx2 {
                var pos1 := -1;
                var pos2 := -1;
                var m := 0;
                while m < k {
                    if order[m] == c1 {
                        pos1 := m;
                    }
                    if order[m] == c2 {
                        pos2 := m;
                    }
                    m := m + 1;
                }
                
                if pos1 == -1 && pos2 == -1 {
                    if k + 2 <= 26 {
                        order[k] := c2;
                        order[k + 1] := c1;
                        var idx_c1 := indexOf(alphabet, c1);
                        var idx_c2 := indexOf(alphabet, c2);
                        used[idx_c1] := true;
                        used[idx_c2] := true;
                        k := k + 2;
                    } else {
                        found := true;
                    }
                } else if pos1 != -1 && pos2 == -1 {
                    return "Impossible";
                } else if pos1 == -1 && pos2 != -1 {
                    return "Impossible";
                }
            }
        }
        i := i + 1;
    }
    
    var remaining_chars: seq<char> := [];
    var m := 0;
    while m < 26 {
        if !used[m] {
            remaining_chars := remaining_chars + [alphabet[m]];
        }
        m := m + 1;
    }
    
    var final_order := "";
    var idx := 0;
    while idx < k {
        final_order := final_order + [order[idx]];
        idx := idx + 1;
    }
    
    var rem_idx := 0;
    while rem_idx < |remaining_chars| {
        final_order := final_order + [remaining_chars[rem_idx]];
        rem_idx := rem_idx + 1;
    }
    
    if forall i :: 1 <= i < n ==> lexCompare(lines[i], lines[i+1], final_order) <= 0 {
        return final_order;
    } else {
        return "Impossible";
    }
}
// </vc-code>

