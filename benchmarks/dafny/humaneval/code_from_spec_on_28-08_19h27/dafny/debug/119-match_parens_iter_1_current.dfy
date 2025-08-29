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
}

lemma MinPrefixConcatenation(s1: seq<char>, s2: seq<char>)
    requires IsValidParenString(s1) && IsValidParenString(s2)
    ensures MinPrefix(s1 + s2) == if MinPrefix(s1) < Balance(s1) + MinPrefix(s2) then MinPrefix(s1) else Balance(s1) + MinPrefix(s2)
{
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
    
    if (Balance(s1) + Balance(s2) == 0 && 
        MinPrefix(s1) >= 0 && 
        Balance(s1) + MinPrefix(s2) >= 0) ||
       (Balance(s1) + Balance(s2) == 0 && 
        MinPrefix(s2) >= 0 && 
        Balance(s2) + MinPrefix(s1) >= 0) {
        result := ['Y', 'e', 's'];
    } else {
        result := ['N', 'o'];
    }
}
// </vc-code>
