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
lemma SeqToSetCorrect(s: seq<int>, x: int)
    ensures x in s <==> x in SeqToSet(s)
{
}

lemma DangerousGroupProperty(group_data: seq<int>)
    ensures is_dangerous_group(group_data) ==> |group_data| > 1
    ensures |group_data| > 1 && is_dangerous_group(group_data) ==> 
        forall i, j :: 1 <= i < |group_data| && 1 <= j < |group_data| ==> 
            group_data[i] != -group_data[j]
{
    if |group_data| > 1 && is_dangerous_group(group_data) {
        var group_members := group_data[1..];
        var member_set := SeqToSet(group_members);
        
        forall i, j | 1 <= i < |group_data| && 1 <= j < |group_data|
            ensures group_data[i] != -group_data[j]
        {
            assert group_data[i] == group_members[i-1];
            assert group_data[j] == group_members[j-1];
            
            SeqToSetCorrect(group_members, group_data[i]);
            assert group_data[i] in member_set;
            
            if group_data[i] == -group_data[j] {
                assert -group_data[j] in member_set;
                SeqToSetCorrect(group_members, group_data[j]);
                assert group_data[j] in member_set;
                assert -group_data[j] in member_set;
                // This contradicts the definition of is_dangerous_group
                assert false;
            }
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
    var found := false;
    
    while i <= m && i < |lines| && !found
        invariant 1 <= i <= m + 1
        invariant i <= |lines| + 1
        invariant !found ==> forall j :: 1 <= j < i && j < |lines| ==> !is_dangerous_group(SplitInts(lines[j]))
        invariant found ==> exists j :: 1 <= j < i && j < |lines| && is_dangerous_group(SplitInts(lines[j]))
    {
        if i < |lines| {
            var group_data := SplitInts(lines[i]);
            if is_dangerous_group(group_data) {
                found := true;
            }
        }
        i := i + 1;
    }
    
    if found {
        assert exists_dangerous_group(stdin_input);
        return "YES\n";
    } else {
        assert !exists_dangerous_group(stdin_input);
        return "NO\n";
    }
}
// </vc-code>

