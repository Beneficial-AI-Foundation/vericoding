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

lemma CalcBalConcatenation(s1: seq<int>, s2: seq<int>)
    ensures CalcBal(s1 + s2, 0, |s1 + s2|, 0) == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, |s2|, 0)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else if |s2| == 0 {
        assert s1 + s2 == s1;
    } else {
        CalcBalConcatenationHelper(s1, s2, 0, |s1|, 0);
    }
}

lemma CalcBalConcatenationHelper(s1: seq<int>, s2: seq<int>, start: int, mid: int, acc: int)
    requires 0 <= start <= mid <= |s1|
    ensures CalcBal(s1 + s2, start, mid + |s2|, acc) == CalcBal(s2, 0, |s2|, 0) + CalcBal(s1, start, mid, acc)
    decreases mid - start
{
    if start == mid {
        assert CalcBal(s1, start, mid, acc) == acc;
        CalcBalShift(s2, 0, |s2|, acc);
    } else {
        CalcBalConcatenationHelper(s1, s2, start, mid - 1, acc);
        assert (s1 + s2)[mid - 1] == s1[mid - 1];
    }
}

lemma CalcBalShift(s: seq<int>, start: int, end: int, acc: int)
    requires 0 <= start <= end <= |s|
    ensures CalcBal(s, start, end, acc) == CalcBal(s, start, end, 0) + acc
    decreases end - start
{
    if start == end {
    } else {
        CalcBalShift(s, start, end - 1, acc);
    }
}

lemma BalanceConcatenation(s1: seq<char>, s2: seq<char>)
    requires IsValidParenString(s1) && IsValidParenString(s2)
    ensures Balance(s1 + s2) == Balance(s1) + Balance(s2)
{
    var seq1 := seq(|s1|, i requires 0 <= i < |s1| => if s1[i] == '(' then 0 else 1);
    var seq2 := seq(|s2|, i requires 0 <= i < |s2| => if s2[i] == '(' then 0 else 1);
    var seqCombined := seq(|s1 + s2|, i requires 0 <= i < |s1 + s2| => if (s1 + s2)[i] == '(' then 0 else 1);
    
    assert seqCombined == seq1 + seq2;
    CalcBalConcatenation(seq1, seq2);
}

lemma MinPrefixConcatenation(s1: seq<char>, s2: seq<char>)
    requires IsValidParenString(s1) && IsValidParenString(s2)
    ensures MinPrefix(s1 + s2) == if MinPrefix(s1) < Balance(s1) + MinPrefix(s2) then MinPrefix(s1) else Balance(s1) + MinPrefix(s2)
{
    MinPrefixConcatenationProof(s1, s2, 0, 0, 0);
}

lemma MinPrefixConcatenationProof(s1: seq<char>, s2: seq<char>, i: int, current: int, minSoFar: int)
    requires IsValidParenString(s1) && IsValidParenString(s2)
    requires 0 <= i <= |s1 + s2|
    decreases |s1 + s2| - i
    ensures MinPrefixAux(s1 + s2, i, current, minSoFar) == 
        if i >= |s1| then
            MinPrefixAux(s2, i - |s1|, current, minSoFar)
        else
            MinPrefixAux(s1 + s2, i + 1, current + (if s1[i] == '(' then 1 else -1), 
                        if current + (if s1[i] == '(' then 1 else -1) < minSoFar then current + (if s1[i] == '(' then 1 else -1) else minSoFar)
{
    if i == |s1 + s2| {
        return;
    } else if i >= |s1| {
        MinPrefixAuxEquiv(s1 + s2, s2, i, i - |s1|, current, minSoFar);
    } else {
        var newCurrent := current + (if s1[i] == '(' then 1 else -1);
        var newMinSoFar := if newCurrent < minSoFar then newCurrent else minSoFar;
        MinPrefixConcatenationProof(s1, s2, i + 1, newCurrent, newMinSoFar);
    }
}

lemma MinPrefixAuxEquiv(combined: seq<char>, s2: seq<char>, i1: int, i2: int, current: int, minSoFar: int)
    requires IsValidParenString(s2)
    requires 0 <= i2 <= |s2|
    requires i1 == |combined| - |s2| + i2
    requires 0 <= i1 <= |combined|
    requires i2 < |s2| ==> combined[i1] == s2[i2]
    ensures MinPrefixAux(combined, i1, current, minSoFar) == MinPrefixAux(s2, i2, current, minSoFar)
    decreases |s2| - i2
{
    if i2 == |s2| {
        return;
    } else {
        var newCurrent := current + (if s2[i2] == '(' then 1 else -1);
        var newMinSoFar := if newCurrent < minSoFar then newCurrent else minSoFar;
        MinPrefixAuxEquiv(combined, s2, i1 + 1, i2 + 1, newCurrent, newMinSoFar);
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
    
    BalanceConcatenation(s1, s2);
    MinPrefixConcatenation(s1, s2);
    BalanceConcatenation(s2, s1);
    MinPrefixConcatenation(s2, s1);
    
    var balanced1 := Balance(s1) + Balance(s2) == 0 && 
                     MinPrefix(s1) >= 0 && 
                     Balance(s1) + MinPrefix(s2) >= 0;
                     
    var balanced2 := Balance(s1) + Balance(s2) == 0 && 
                     MinPrefix(s2) >= 0 && 
                     Balance(s2) + MinPrefix(s1) >= 0;
    
    if balanced1 || balanced2 {
        result := ['Y', 'e', 's'];
        
        if balanced1 {
            assert Balance(s1 + s2) == 0;
            assert MinPrefix(s1 + s2) >= 0;
            assert IsBalanced(s1 + s2);
        } else {
            assert Balance(s2 + s1) == 0;
            assert MinPrefix(s2 + s1) >= 0;
            assert IsBalanced(s2 + s1);
        }
    } else {
        result := ['N', 'o'];
        
        assert !balanced1 && !balanced2;
        assert !(Balance(s1 + s2) == 0 && MinPrefix(s1 + s2) >= 0);
        assert !(Balance(s2 + s1) == 0 && MinPrefix(s2 + s1) >= 0);
        assert !IsBalanced(s1 + s2);
        assert !IsBalanced(s2 + s1);
    }
}
// </vc-code>
