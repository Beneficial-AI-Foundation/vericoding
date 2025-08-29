function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
function CalcBal(s: seq<char>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == '(' then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

function IsBalanced(s: seq<char>): bool
    requires forall k :: 0 <= k < |s| ==> s[k] == '(' || s[k] == ')'
{
    CalcBal(s, 0, |s|, 0) == 0
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def match_parens(l : list[str]) -> str
You are given a list of two strings, both strings consist of open parentheses '(' or close parentheses ')' only. Your job is to check if it is possible to concatenate the two strings in some order, that the resulting string will be good. A string S is considered to be good if and only if all parentheses in S are balanced. For example: the string '(())()' is good, while the string '())' is not. Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.
*/
// </vc-description>

// <vc-spec>
method MatchParens(l: seq<string>) returns (result: string)
    requires |l| == 2
    requires forall i :: 0 <= i < |l| ==> forall k :: 0 <= k < |l[i]| ==> l[i][k] == '(' || l[i][k] == ')'
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> (IsBalanced(l[0] + l[1]) || IsBalanced(l[1] + l[0]))
// </vc-spec>
// <vc-code>
{
    var s1 := l[0];
    var s2 := l[1];
    var concat1 := s1 + s2;
    var concat2 := s2 + s1;
    var bal1 := CalcBal(concat1, 0, |concat1|, 0);
    var bal2 := CalcBal(concat2, 0, |concat2|, 0);
    if bal1 == 0 || bal2 == 0 {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>
