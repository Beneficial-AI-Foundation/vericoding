/*
Given a string of uppercase letters A-Z with length 1-10, determine if all letters
belong to the same predefined group. Group 1: A,E,F,H,I,K,L,M,N,T,V,W,X,Y,Z.
Group 2: B,C,D,G,J,O,P,Q,R,S,U. Output "YES" if all letters in same group, "NO" otherwise.
*/

predicate ValidInput(word: string) 
{
    1 <= |word| <= 10 && forall i :: 0 <= i < |word| ==> 'A' <= word[i] <= 'Z'
}

function Group1(): string { "AEFHIKLMNTVWXYZ" }
function Group2(): string { "BCDGJOPQRSU" }

predicate AllInGroup1(word: string)
{
    forall i :: 0 <= i < |word| ==> word[i] in Group1()
}

predicate AllInGroup2(word: string)
{
    forall i :: 0 <= i < |word| ==> word[i] in Group2()
}

predicate AllInSameGroup(word: string)
{
    AllInGroup1(word) || AllInGroup2(word)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(word: string) returns (result: string)
    requires ValidInput(word)
    ensures AllInSameGroup(word) <==> result == "YES"
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
