function SplitLines(s: string): seq<string>
    requires |s| >= 0
    ensures |SplitLines(s)| >= 0
    ensures |s| == 0 ==> |SplitLines(s)| == 0
    ensures |s| > 0 ==> |SplitLines(s)| >= 1
    ensures forall i :: 0 <= i < |SplitLines(s)| ==> |SplitLines(s)[i]| >= 0
{
    if |s| == 0 then [] else [s]
}

function SplitInts(s: string): seq<int>
    requires |s| >= 0
    ensures |SplitInts(s)| >= 0
{
    []
}

function SeqToSet(s: seq<int>): set<int>
{
    set x | x in s
}

function is_dangerous_group(group_data: seq<int>): bool
{
    if |group_data| <= 1 then false
    else
        var group_members := group_data[1..];
        var member_set := SeqToSet(group_members);
        forall member :: member in member_set ==> -member !in member_set
}

predicate exists_dangerous_group(stdin_input: string)
    requires |stdin_input| > 0
{
    var lines := SplitLines(stdin_input);
    if |lines| == 0 then false
    else
        var first_line := SplitInts(lines[0]);
        if |first_line| < 2 then false
        else
            var n := first_line[0];
            var m := first_line[1];
            if m <= 0 || n <= 0 then false
            else
                exists i :: 1 <= i <= m && i < |lines| && 
                    is_dangerous_group(SplitInts(lines[i]))
}

// <vc-helpers>
function SplitAtNewline(s: string): (string, string)
    ensures |s| == 0 ==> result.0 == "" && result.1 == ""
    ensures |result.0| <= |s|
    ensures |result.1| <= |s|
{
    if |s| == 0 then ("", "")
    else if s[0] == '\n' then ("", s[1..])
    else
        var (prefix, suffix) := SplitAtNewline(s[1..]);
        (s[0] + prefix, suffix)
}

lemma {:induction s} SplitLinesLemma(s: string)
    ensures SplitLines(s) ==
        if |s| == 0 then []
        else if s[0] == '\n' then [""] + SplitLines(s[1..])
        else
            var (prefix, suffix) := SplitAtNewline(s);
            [prefix] + SplitLines(suffix)
{
    if |s| > 0 {
        if s[0] == '\n' {
            SplitLinesLemma(s[1..]);
        } else {
            var (prefix, suffix) := SplitAtNewline(s[1..]);
            SplitLinesLemma(suffix);
        }
    }
}

function {:inline} IsDigit(c: char): bool {
    '0' <= c <= '9'
}

function ParseInt(s: string): (int, string)
    requires |s| > 0 && IsDigit(s[0])
    ensures |result.1| <= |s|
{
    // Manual implementation to avoid while loop syntax error
    if |s| == 0 || !IsDigit(s[0]) then (0, s)
    else
        var num := 0;
        var i := 0;
        while i < |s| && IsDigit(s[i])
            invariant 0 <= i <= |s|
            invariant num >= 0
        {
            num := num * 10 + (s[i] as int - '0' as int);
            i := i + 1;
        }
        (num, s[i..])
}

function SplitInts(s: string): seq<int>
    requires |s| >= 0
    ensures |SplitInts(s)| >= 0
{
    SplitIntsHelper(s, [])
}

function SplitIntsHelper(s: string, acc: seq<int>): seq<int>
    ensures |result| >= |acc|
{
    if |s| == 0 then acc
    else if IsDigit(s[0]) then
        var (num, rest) := ParseInt(s);
        SplitIntsHelper(rest, acc + [num])
    else
        SplitIntsHelper(s[1..], acc)
}

lemma {:induction s, acc} SplitIntsHelperLemma(s: string, acc: seq<int>)
    ensures SplitInts(s) == SplitIntsHelper(s, [])
{
    if |s| > 0 {
        if IsDigit(s[0]) {
            var (num, rest) := ParseInt(s);
            SplitIntsHelperLemma(rest, [num]);
        } else {
            SplitIntsHelperLemma(s[1..], []);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures result == "YES\n" || result == "NO\n"
    ensures (result == "YES\n") <==> exists_dangerous_group(stdin_input)
    ensures (result == "NO\n") <==> !exists_dangerous_group(stdin_input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(stdin_input);
    if |lines| == 0 {
        result := "NO\n";
        return;
    }
    
    var first_line := SplitInts(lines[0]);
    if |first_line| < 2 {
        result := "NO\n";
        return;
    }
    
    var n := first_line[0];
    var m := first_line[1];
    
    if m <= 0 || n <= 0 {
        result := "NO\n";
        return;
    }
    
    var i := 1;
    while i <= m && i < |lines|
        invariant 1 <= i <= |lines| + 1
        invariant i <= m + 1
    {
        var group_data := SplitInts(lines[i]);
        if |group_data| > 1 {
            var group_members := group_data[1..];
            var member_set := SeqToSet(group_members);
            if forall member :: member in member_set ==> -member !in member_set {
                result := "YES\n";
                return;
            }
        }
        i := i + 1;
    }
    
    result := "NO\n";
}
// </vc-code>

