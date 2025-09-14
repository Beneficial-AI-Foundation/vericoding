predicate ValidInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 &&
    var O := lines[0];
    var E := lines[1];
    var a := |O|;
    var b := |E|;
    (a == b || a == b + 1) &&
    (a > 0 || b == 0)
}

function GetO(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[0]
}

function GetE(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[1]
}

function CorrectResult(input: string): string
    requires ValidInput(input)
{
    var O := GetO(input);
    var E := GetE(input);
    var a := |O|;
    var b := |E|;
    if a == b then
        InterleaveEqual(O, E)
    else
        InterleaveUnequal(O, E)
}

function InterleaveEqual(O: string, E: string): string
    requires |O| == |E|
{
    if |O| == 0 then ""
    else [O[0], E[0]] + InterleaveEqual(O[1..], E[1..])
}

function InterleaveUnequal(O: string, E: string): string
    requires |O| == |E| + 1
{
    if |E| == 0 then O
    else [O[0], E[0]] + InterleaveUnequal(O[1..], E[1..])
}

// <vc-helpers>
function split(s: string, delimiter: char): seq<string>

lemma InterleaveEqualCorrectness(O: string, E: string, i: nat, result: string)
    requires |O| == |E|
    requires i <= |O|
    requires |result| == 2 * i
    requires forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
    ensures result + InterleaveEqual(O[i..], E[i..]) == InterleaveEqual(O, E)
    decreases |O| - i
{
    if i == |O| {
        assert O[i..] == "";
        assert E[i..] == "";
        assert InterleaveEqual("", "") == "";
        assert result + "" == result;
        InterleaveEqualBuildUp(O, E, i, result);
    } else {
        assert O[i..][0] == O[i];
        assert E[i..][0] == E[i];
        assert O[i..][1..] == O[i+1..];
        assert E[i..][1..] == E[i+1..];
        
        calc {
            result + InterleaveEqual(O[i..], E[i..]);
        ==
            result + ([O[i], E[i]] + InterleaveEqual(O[i+1..], E[i+1..]));
        ==
            (result + [O[i], E[i]]) + InterleaveEqual(O[i+1..], E[i+1..]);
        }
        
        var result' := result + [O[i], E[i]];
        assert |result'| == 2 * (i + 1);
        assert forall k :: 0 <= k < i+1 ==> result'[2*k] == O[k] && result'[2*k+1] == E[k];
        InterleaveEqualCorrectness(O, E, i+1, result');
        assert result' + InterleaveEqual(O[i+1..], E[i+1..]) == InterleaveEqual(O, E);
    }
}

lemma InterleaveEqualBuildUp(O: string, E: string, i: nat, result: string)
    requires |O| == |E|
    requires i == |O|
    requires |result| == 2 * i
    requires forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
    ensures result == InterleaveEqual(O, E)
    decreases i
{
    if i == 0 {
        assert O == "";
        assert E == "";
        assert result == "";
        assert InterleaveEqual("", "") == "";
    } else {
        var result_prev := result[..2*(i-1)];
        assert |result_prev| == 2 * (i-1);
        assert forall k :: 0 <= k < i-1 ==> result_prev[2*k] == O[..i-1][k] && result_prev[2*k+1] == E[..i-1][k];
        
        InterleaveEqualBuildUp(O[..i-1], E[..i-1], i-1, result_prev);
        assert result_prev == InterleaveEqual(O[..i-1], E[..i-1]);
        
        assert result == result_prev + [O[i-1], E[i-1]];
        
        calc {
            InterleaveEqual(O, E);
        ==
            [O[0], E[0]] + InterleaveEqual(O[1..], E[1..]);
        ==  { if i-1 > 0 { InterleaveEqualUnfold(O, E, i-1); } }
            InterleaveEqual(O[..i-1], E[..i-1]) + [O[i-1], E[i-1]] + InterleaveEqual(O[i..], E[i..]);
        ==  { assert O[i..] == ""; assert E[i..] == ""; }
            InterleaveEqual(O[..i-1], E[..i-1]) + [O[i-1], E[i-1]];
        ==
            result_prev + [O[i-1], E[i-1]];
        ==
            result;
        }
    }
}

lemma InterleaveEqualUnfold(O: string, E: string, j: nat)
    requires |O| == |E|
    requires 0 < j < |O|
    ensures InterleaveEqual(O, E) == InterleaveEqual(O[..j], E[..j]) + InterleaveEqual(O[j..], E[j..])
    decreases j
{
    if j == 1 {
        assert InterleaveEqual(O, E) == [O[0], E[0]] + InterleaveEqual(O[1..], E[1..]);
        assert O[..1] == [O[0]];
        assert E[..1] == [E[0]];
        assert InterleaveEqual(O[..1], E[..1]) == [O[0], E[0]];
        assert O[1..] == O[j..];
        assert E[1..] == E[j..];
    } else {
        calc {
            InterleaveEqual(O, E);
        ==
            [O[0], E[0]] + InterleaveEqual(O[1..], E[1..]);
        ==  { InterleaveEqualUnfold(O[1..], E[1..], j-1); }
            [O[0], E[0]] + InterleaveEqual(O[1..][..j-1], E[1..][..j-1]) + InterleaveEqual(O[1..][j-1..], E[1..][j-1..]);
        ==  { assert O[1..][..j-1] == O[1..j]; assert E[1..][..j-1] == E[1..j]; 
              assert O[1..][j-1..] == O[j..]; assert E[1..][j-1..] == E[j..]; }
            [O[0], E[0]] + InterleaveEqual(O[1..j], E[1..j]) + InterleaveEqual(O[j..], E[j..]);
        ==  { InterleaveEqualPrefix(O[..j], E[..j]); }
            InterleaveEqual(O[..j], E[..j]) + InterleaveEqual(O[j..], E[j..]);
        }
    }
}

lemma InterleaveEqualPrefix(O: string, E: string)
    requires |O| == |E| >= 1
    ensures InterleaveEqual(O, E) == [O[0], E[0]] + InterleaveEqual(O[1..], E[1..])
{
}

lemma InterleaveUnequalCorrectness(O: string, E: string, i: nat, result: string)
    requires |O| == |E| + 1
    requires i <= |E|
    requires |result| == 2 * i
    requires forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
    ensures result + InterleaveUnequal(O[i..], E[i..]) == InterleaveUnequal(O, E)
    decreases |E| - i
{
    if i == |E| {
        assert E[i..] == "";
        assert |O[i..]| == 1;
        assert O[i..] == [O[i]];
        assert InterleaveUnequal(O[i..], "") == O[i..];
        InterleaveUnequalBuildUp(O, E, i, result);
    } else {
        var result' := result + [O[i], E[i]];
        assert |result'| == 2 * (i + 1);
        assert forall k :: 0 <= k < i+1 ==> result'[2*k] == O[k] && result'[2*k+1] == E[k];
        
        calc {
            result + InterleaveUnequal(O[i..], E[i..]);
        ==
            result + ([O[i], E[i]] + InterleaveUnequal(O[i+1..], E[i+1..]));
        ==
            result' + InterleaveUnequal(O[i+1..], E[i+1..]);
        }
        
        InterleaveUnequalCorrectness(O, E, i+1, result');
    }
}

lemma InterleaveUnequalBuildUp(O: string, E: string, i: nat, result: string)
    requires |O| == |E| + 1
    requires i == |E|
    requires |result| == 2 * i
    requires forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
    ensures result + [O[i]] == InterleaveUnequal(O, E)
{
    if i == 0 {
        assert E == "";
        assert result == "";
        assert InterleaveUnequal(O, "") == O;
        assert |O| == 1;
        assert O == [O[0]];
    } else {
        var result_prev := result[..2*(i-1)];
        assert |result_prev| == 2 * (i-1);
        assert forall k :: 0 <= k < i-1 ==> result_prev[2*k] == O[..i-1][k] && result_prev[2*k+1] == E[..i-1][k];
        
        InterleaveUnequalBuildUp(O[..i], E[..i-1], i-1, result_prev);
        assert result_prev + [O[i-1]] == InterleaveUnequal(O[..i], E[..i-1]);
        
        assert result == result_prev + [O[i-1], E[i-1]];
        
        if i == 1 {
            calc {
                InterleaveUnequal(O, E);
            ==
                [O[0], E[0]] + InterleaveUnequal(O[1..], E[1..]);
            ==  { assert E[1..] == ""; assert InterleaveUnequal(O[1..], "") == O[1..]; assert |O[1..]| == 1; }
                [O[0], E[0]] + [O[1]];
            ==
                result + [O[i]];
            }
        } else {
            InterleaveUnequalUnfold2(O, E, i);
            calc {
                InterleaveUnequal(O, E);
            ==
                InterleaveEqual(O[..i], E[..i]) + [O[i]];
            ==  { InterleaveEqualBuildUp(O[..i], E[..i], i, result); }
                result + [O[i]];
            }
        }
    }
}

lemma InterleaveUnequalUnfold2(O: string, E: string, j: nat)
    requires |O| == |E| + 1
    requires 0 < j == |E|
    ensures InterleaveUnequal(O, E) == 
            (if j == 1 then [O[0], E[0]] + O[1..] 
             else InterleaveEqual(O[..j], E[..j]) + [O[j]])
{
    if j == 1 {
        assert E[1..] == "";
        assert InterleaveUnequal(O[1..], E[1..]) == O[1..];
    } else {
        InterleaveUnequalRecursive(O, E, j);
    }
}

lemma InterleaveUnequalRecursive(O: string, E: string, j: nat)
    requires |O| == |E| + 1
    requires 1 < j == |E|
    ensures InterleaveUnequal(O, E) == InterleaveEqual(O[..j], E[..j]) + [O[j]]
{
    if j == 2 {
        calc {
            InterleaveUnequal(O, E);
        ==
            [O[0], E[0]] + InterleaveUnequal(O[1..], E[1..]);
        ==
            [O[0], E[0]] + [O[1], E[1]] + InterleaveUnequal(O[2..], E[2..]);
        ==  { assert E[2..] == ""; assert InterleaveUnequal(O[2..], "") == O[2..]; }
            [O[0], E[0]] + [O[1], E[1]] + [O[2]];
        ==  { 
            assert [O[0], E[0]] + [O[1], E[1]] == [O[0], E[0], O[1], E[1]];
            assert InterleaveEqual(O[..2], E[..2]) == [O[0], E[0]] + InterleaveEqual(O[..2][1..], E[..2][1..]);
            assert O[..2][1..] == [O[1]];
            assert E[..2][1..] == [E[1]];
            assert InterleaveEqual([O[1]], [E[1]]) == [O[1], E[1]];
        }
            InterleaveEqual(O[..2], E[..2]) + [O[2]];
        }
    } else {
        calc {
            InterleaveUnequal(O, E);
        ==
            [O[0], E[0]] + InterleaveUnequal(O[1..], E[1..]);
        ==  { InterleaveUnequalRecursive(O[1..], E[1..], j-1); }
            [O[0], E[0]] + InterleaveEqual(O[1..][..j-1], E[1..][..j-1]) + [O[1..][j-1]];
        ==  { assert O[1..][..j-1] == O[1..j]; assert E[1..][..j-1] == E[1..j]; assert O[1..][j-1] == O[j]; }
            [O[0], E[0]] + InterleaveEqual(O[1..j], E[1..j]) + [O[j]];
        ==  { InterleaveEqualBuildFromPrefix(O[..j], E[..j]); }
            InterleaveEqual(O[..j], E[..j]) + [O[j]];
        }
    }
}

lemma InterleaveEqualBuildFromPrefix(O: string, E: string)
    requires |O| == |E| >= 1
    ensures InterleaveEqual(O, E) == [O[0], E[0]] + InterleaveEqual(O[1..], E[1..])
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == CorrectResult(input)
// </vc-spec>
// <vc-code>
{
    var lines := split(input, '\n');
    var O := lines[0];
    var E := lines[1];
    var a := |O|;
    var b := |E|;
    
    result := "";
    var i := 0;
    
    if a == b {
        while i < a
            invariant 0 <= i <= a
            invariant |result| == 2 * i
            invariant forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
            invariant result + InterleaveEqual(O[i..], E[i..]) == InterleaveEqual(O, E)
        {
            InterleaveEqualCorrectness(O, E, i, result);
            result := result + [O[i], E[i]];
            i := i + 1;
        }
    } else {
        while i < b
            invariant 0 <= i <= b
            invariant |result| == 2 * i
            invariant forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
            invariant result + InterleaveUnequal(O[i..], E[i..]) == InterleaveUnequal(O, E)
        {
            InterleaveUnequalCorrectness(O, E, i, result);
            result := result + [O[i], E[i]];
            i := i + 1;
        }
        result := result + [O[b]];
    }
}
// </vc-code>

