function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
function Balance(s: seq<char>) : int
{
    CalcBal(seq(|s|, i requires 0 <= i < |s| => if s[i] == '(' then 0 else 1), 0, |s|, 0)
}

function MinPrefix(s: seq<char>) : int
{
    MinPrefixAux(s, 0, 0, 0)
}

function MinPrefixAux(s: seq<char>, i: int, current: int, minSoFar: int) : int
    requires 0 <= i <= |s|
    decreases |s| - i, if current >= 0 then 0 else -current
{
    if i == |s| then minSoFar
    else 
        var newCurrent := current + (if s[i] == '(' then 1 else -1);
        MinPrefixAux(s, i + 1, newCurrent, if newCurrent < minSoFar then newCurrent else minSoFar)
}

predicate IsValidParenString(s: seq<char>)
{
    forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
}

predicate IsBalanced(s: seq<char>)
    requires IsValidParenString(s)
{
    Balance(s) == 0 && MinPrefix(s) >= 0
}

lemma BalanceConcatenation(s1: seq<char>, s2: seq<char>)
    requires IsValidParenString(s1) && IsValidParenString(s2)
    ensures Balance(s1 + s2) == Balance(s1) + Balance(s2)
{
    assert seq(|s1 + s2|, i requires 0 <= i < |s1 + s2| => if (s1 + s2)[i] == '(' then 0 else 1) == 
           seq(|s1|, i requires 0 <= i < |s1| => if s1[i] == '(' then 0 else 1) + 
           seq(|s2|, i requires 0 <= i < |s2| => if s2[i] == '(' then 0 else 1);
}

lemma MinPrefixConcatenation(s1: seq<char>, s2: seq<char>)
    requires IsValidParenString(s1) && IsValidParenString(s2)
    ensures MinPrefix(s1 + s2) == if MinPrefix(s1) < Balance(s1) + MinPrefix(s2) then MinPrefix(s1) else Balance(s1) + MinPrefix(s2)
{
    MinPrefixConcatenationHelper(s1, s2);
}

lemma MinPrefixConcatenationHelper(s1: seq<char>, s2: seq<char>)
    requires IsValidParenString(s1) && IsValidParenString(s2)
    ensures MinPrefix(s1 + s2) == if MinPrefix(s1) < Balance(s1) + MinPrefix(s2) then MinPrefix(s1) else Balance(s1) + MinPrefix(s2)
{
    var combined := s1 + s2;
    assert MinPrefix(combined) == MinPrefixAux(combined, 0, 0, 0);
    
    MinPrefixSplit(s1, s2, 0, 0, 0);
}

lemma MinPrefixSplit(s1: seq<char>, s2: seq<char>, current: int, minSoFar: int, processed: int)
    requires IsValidParenString(s1) && IsValidParenString(s2)
    requires 0 <= processed <= |s1|
    decreases |s1| - processed
    ensures MinPrefixAux(s1 + s2, processed, current, minSoFar) == 
            if processed == |s1| then
                var newMin := if MinPrefixAux(s2, 0, current, minSoFar) < minSoFar then MinPrefixAux(s2, 0, current, minSoFar) else minSoFar;
                newMin
            else
                MinPrefixAux(s1 + s2, processed + 1, current + (if s1[processed] == '(' then 1 else -1), 
                            if current + (if s1[processed] == '(' then 1 else -1) < minSoFar then current + (if s1[processed] == '(' then 1 else -1) else minSoFar)
{
    if processed == |s1| {
        assert MinPrefixAux(s1 + s2, processed, current, minSoFar) == MinPrefixAux(s2, 0, current, minSoFar);
    } else {
        MinPrefixSplit(s1, s2, current + (if s1[processed] == '(' then 1 else -1), 
                      if current + (if s1[processed] == '(' then 1 else -1) < minSoFar then current + (if s1[processed] == '(' then 1 else -1) else minSoFar,
                      processed + 1);
    }
}

lemma ValidParenStringConcatenation(s1: seq<char>, s2: seq<char>)
    requires IsValidParenString(s1) && IsValidParenString(s2)
    ensures IsValidParenString(s1 + s2)
{
    forall i | 0 <= i < |s1 + s2|
        ensures (s1 + s2)[i] == '(' || (s1 + s2)[i] == ')'
    {
        if i < |s1| {
            assert (s1 + s2)[i] == s1[i];
            assert s1[i] == '(' || s1[i] == ')';
        } else {
            assert (s1 + s2)[i] == s2[i - |s1|];
            assert s2[i - |s1|] == '(' || s2[i - |s1|] == ')';
        }
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def match_parens(l : list[str]) -> str
You are given a list of two strings, both strings consist of open parentheses '(' or close parentheses ')' only. Your job is to check if it is possible to concatenate the two strings in some order, that the resulting string will be good. A string S is considered to be good if and only if all parentheses in S are balanced. For example: the string '(())()' is good, while the string '())' is not. Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.
*/
// </vc-description>

// <vc-spec>
method match_parens(l: seq<seq<char>>) returns (result: seq<char>)
    requires |l| == 2
    requires forall i :: 0 <= i < |l| ==> IsValidParenString(l[i])
    ensures result == ['Y', 'e', 's'] || result == ['N', 'o']
    ensures result == ['Y', 'e', 's'] <==> 
        (IsBalanced(l[0] + l[1]) || IsBalanced(l[1] + l[0]))
// </vc-spec>
// <vc-code>
{
    var s1 := l[0];
    var s2 := l[1];
    
    ValidParenStringConcatenation(s1, s2);
    ValidParenStringConcatenation(s2, s1);
    
    var balanced1 := Balance(s1) + Balance(s2) == 0 && 
                     MinPrefix(s1) >= 0 && 
                     Balance(s1) + MinPrefix(s2) >= 0;
                     
    var balanced2 := Balance(s1) + Balance(s2) == 0 && 
                     MinPrefix(s2) >= 0 && 
                     Balance(s2) + MinPrefix(s1) >= 0;
    
    if balanced1 || balanced2 {
        result := ['Y', 'e', 's'];
        
        if balanced1 {
            BalanceConcatenation(s1, s2);
            MinPrefixConcatenation(s1, s2);
            assert IsBalanced(s1 + s2);
        } else {
            BalanceConcatenation(s2, s1);  
            MinPrefixConcatenation(s2, s1);
            assert IsBalanced(s2 + s1);
        }
    } else {
        result := ['N', 'o'];
        
        BalanceConcatenation(s1, s2);
        MinPrefixConcatenation(s1, s2);
        BalanceConcatenation(s2, s1);
        MinPrefixConcatenation(s2, s1);
        
        assert !IsBalanced(s1 + s2);
        assert !IsBalanced(s2 + s1);
    }
}
// </vc-code>
