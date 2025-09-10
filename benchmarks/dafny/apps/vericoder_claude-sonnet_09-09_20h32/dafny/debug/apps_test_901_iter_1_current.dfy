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
lemma SplitLinesLength(s: string)
    requires |s| > 0
    ensures |SplitLines(s)| >= 1
{
}

lemma SplitIntsEmpty(s: string)
    ensures |SplitInts(s)| == 0
{
}

lemma SeqToSetProperty(s: seq<int>, x: int)
    ensures (x in SeqToSet(s)) <==> (x in s)
{
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
        return "NO\n";
    }
    
    var first_line := SplitInts(lines[0]);
    
    if |first_line| < 2 {
        return "NO\n";
    }
    
    var n := first_line[0];
    var m := first_line[1];
    
    if m <= 0 || n <= 0 {
        return "NO\n";
    }
    
    var i := 1;
    while i <= m && i < |lines|
        invariant 1 <= i <= m + 1
        invariant i <= |lines| + 1
        invariant forall j :: 1 <= j < i && j < |lines| ==> !is_dangerous_group(SplitInts(lines[j]))
    {
        var group_data := SplitInts(lines[i]);
        if is_dangerous_group(group_data) {
            return "YES\n";
        }
        i := i + 1;
    }
    
    return "NO\n";
}
// </vc-code>

